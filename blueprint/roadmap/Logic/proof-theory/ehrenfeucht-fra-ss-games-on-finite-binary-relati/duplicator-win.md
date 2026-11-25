# Duplicator Win

Let $R$ and $S$ be Boolean-valued binary relations on $\{0, \dots, n-1\}$ and $\{0, \dots, m-1\}$, and let a position be a finite list $P$ of pairs $(a, b)$ with $a < n$, $b < m$. Duplicator wins the $k$-round Ehrenfeucht–Fraïssé game between $R$ and $S$ from $P$, defined by recursion on $k$:

- with $k = 0$ rounds left, Duplicator wins from $P$ if and only if $P$ is a partial isomorphism between $R$ and $S$;
- with $k + 1$ rounds left, Duplicator wins from $P$ if and only if for every $a < n$ there is $b < m$, and for every $b < m$ there is $a < n$, such that Duplicator wins the $k$-round game from the position obtained by adding the pair $(a, b)$ to $P$.
