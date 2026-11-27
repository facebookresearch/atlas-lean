# Thorup's high independence of double tabulation

Let $\Sigma = [2^b]$, $c \ge 1$ and $d \ge 6c$, and let the first-stage function $h_0 : \Sigma^c \to \Sigma^d$ be simple tabulation with fully random character tables (Thorup, Theorem 1). Asymptotically in $|\Sigma|$, under Thorup's assumptions $c = |\Sigma|^{o(1)}$ and $(c + d)^c = |\Sigma|^{o(1)}$, and with $k = |\Sigma|^{1/(5c)}$: with probability $1 - o(|\Sigma|^{2 - d/(2c)})$ over $h_0$, the function $h_0$ is $k$-unique, and then the double tabulation function $h_1 \circ h_0$ is $k$-wise independent over the choice of $h_1$, whose $d$ character tables are independent of each other and each $k$-wise independent (fully random suffices). In particular, with $d = 6c$, double tabulation gives, with high probability over $h_0$, a $|\Sigma|^{\Omega(1/c)}$-wise independent family evaluated with $c + d = 7c$ table lookups from $(c + d)|\Sigma|$ table entries. The first-stage character tables may instead be $k$-wise independent and independent of each other (Thorup, remark after Theorem 1).

## Proof sketch

Thorup's Theorem 1(a) shows that with the stated probability $h_0$ is $k$-unique: every nonempty set of at most $k$ keys has a unique output position character, a position $j$ and a character $a$ such that exactly one key $x$ of the set has $h_0(x)_j = a$. Siegel's lemma (Thorup, Lemma 2) then gives $k$-wise independence of $h_1 \circ h_0$, by induction on the set size: the entry of the $j$-th table of $h_1$ at the unique character is used by one key only and masks its value uniformly and independently of the others.

## Depends on

- [Double tabulation hashing](double-tabulation-hashing.md)
- [k-wise independent hash family](k-wise-independent-hash-family.md)
- [k-unique maps composed with simple tabulation are k-wise independent](../limited-independence-hash-families/k-uniqueness-and-siegel-peeling.md)

## Sources

- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), 2013; arXiv:1311.3121.
