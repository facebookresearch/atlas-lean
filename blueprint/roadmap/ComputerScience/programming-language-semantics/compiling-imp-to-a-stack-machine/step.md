# Step relation of the stack machine

Let $P$ be a program, that is a list of instructions,
and write $a :: \sigma$ for the stack with top $a$ above the stack $\sigma$. A configuration
$(pc, \sigma, s)$ steps to a configuration $c'$ under $P$ exactly when $pc < |P|$ and, for the
instruction at position $pc$ of $P$ (counted from $0$), one of the following holds, where
$s[x \mapsto v]$ is the state $s$ with variable $x$ set to $v$.

- $\mathsf{push}\ n$: $c' = (pc + 1, n :: \sigma, s)$.
- $\mathsf{load}\ x$: $c' = (pc + 1, s(x) :: \sigma, s)$.
- $\mathsf{store}\ x$: $\sigma = v :: \tau$ and $c' = (pc + 1, \tau, s[x \mapsto v])$.
- $\mathsf{add}$, $\mathsf{sub}$, $\mathsf{mul}$: $\sigma = a :: b :: \tau$ and
  $c' = (pc + 1, r :: \tau, s)$, where $r$ is $b + a$, $\max(b - a, 0)$ or $b \cdot a$ respectively.
- $\mathsf{eq}$, $\mathsf{le}$: $\sigma = a :: b :: \tau$ and $c' = (pc + 1, r :: \tau, s)$,
  where $r$ is $1$ if $b = a$, respectively $b \le a$, and $r = 0$ otherwise.
- $\mathsf{not}$: $\sigma = a :: \tau$ and $c' = (pc + 1, r :: \tau, s)$, where $r = 1$ if $a = 0$
  and $r = 0$ otherwise.
- $\mathsf{and}$: $\sigma = a :: b :: \tau$ and $c' = (pc + 1, r :: \tau, s)$, where $r = 1$ if
  $b \ne 0$ and $a \ne 0$, and $r = 0$ otherwise.
- $\mathsf{jump}\ t$: $c' = (t, \sigma, s)$.
- $\mathsf{jumpIfZero}\ t$: either $\sigma = 0 :: \tau$ and $c' = (t, \tau, s)$, or
  $\sigma = (n + 1) :: \tau$ for some $n$ and $c' = (pc + 1, \tau, s)$.

For binary instructions the top of the stack $a$ is thus the right operand and the value below it
$b$ is the left operand.
