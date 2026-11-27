# Stage segments of a restricted Gaussian partition

Let $q$ be a natural number, let
$(d_0, m_0), \dots, (d_{\ell-1}, m_{\ell-1})$ be blocks, let $C_0, C_1, \dots$ be chains of
branch steps, let $F_0, F_1, \dots$ be lists of natural numbers, and let $i$ and $k$ be natural
numbers; blocks, chains and lists are indexed from $0$. With $p_h = \sum_{g < h} m_g d_g$, the
basic segment of block $h$ is the list of $\sum_{j=0}^{m_h - 1} q^{p_h + j d_h}$ copies of $d_h$.
A step $(a, b, c)$ acts on a list by deleting its last $c$ entries equal to $a + b$ and putting
$c$ copies of $a$ followed by $c q^a$ copies of $b$ where the first deleted entry was, after the
entries before it and before the remaining entries after it (a step with $c = 0$ changes
nothing); it fails if the list has fewer than $c$ entries equal to $a + b$.

The stage segments at $(i, k)$ form the list of $\ell$ segments whose entry for block $h$ is
$F_h$ if $h < i$; the result of applying the first $k + 1$ steps of $C_i$ in order to the basic
segment of block $i$ if $h = i$ (all steps of $C_i$ if it has at most $k + 1$, and none if there
is no chain $C_i$); and the basic segment of block $h$ if $h > i$. They are undefined if $F_h$ is
missing for some block $h < i$ or one of these steps fails.
