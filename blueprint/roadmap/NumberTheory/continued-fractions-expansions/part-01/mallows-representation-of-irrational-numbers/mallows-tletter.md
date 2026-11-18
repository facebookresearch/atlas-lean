# The letter rule of $T$

For a truth value $b$ and letters $a, a'$ of
$\{O_L, E_R, O_R, E_L\}$, the letter $\tau(b, a, a') \in \{L, M, R\}$ is defined as follows. If
$b$ is true, it is $L$ when $a = O_L$ and $R$ otherwise. If $b$ is false, it is $M$ when
$a \ne a'$, $L$ when $a = a' = O_R$, and $R$ when $a = a' \ne O_R$.

If $o(1) < o(2) < \cdots$ are the positions of the letters $O_L$ and $O_R$ in a sequence $x$,
then $T_i(x) = \tau(b, x_{o(i)}, x_{o(i+1)})$, where $b$ is true exactly when
$o(i + 1) = o(i) + 1$.

## Sources

- Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25 (2025), Article A78, Section 3 (definition of `T_i`).
