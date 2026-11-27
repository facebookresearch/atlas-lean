# Cutting a bit string into blocks

The $n$-bit blocks of a bit string $P$ are the result of [cutting at most $\lfloor |P|/n \rfloor$ blocks](blocks-fuel.md) off $P$, with natural-number floor division. For $n > 0$ these are the first $\lfloor |P|/n \rfloor$ blocks of $n$ consecutive bits, and the last $|P| \bmod n$ bits are dropped (the block decomposition $x_1, \dots, x_B$ of Katz and Lindell, Construction 5.3, where $n \mid |P|$). At $n = 0$, $\lfloor |P|/0 \rfloor = 0$, so the list of blocks is empty.

$|P|$ is computed once, so for $n > 0$ this is linear in $|P|$.
