# Exclusion principle and Sperner bound for stable Lotka–Volterra communities

**Model.** For $N$ species with populations $p_i\ge0$,

$$p_i'=p_i\Bigl(a_i-\sum_{j=1}^NB_{ij}p_j\Bigr),\qquad i\in\mathcal N=\{1,\dots,N\}.$$

The support of an equilibrium $\bar p\ge0$ is its *community* $\mathcal I=\{i:\bar p_i>0\}$. $\bar p$ is *internally stable* if the community matrix $-\mathrm{diag}(\bar p_{\mathcal I})B_{\mathcal I\mathcal I}$ is stable, *strictly stable* if moreover $a_i-(B\bar p)_i<0$ for all $i\notin\mathcal I$ (no absent species can invade), and *$\mathcal Q$-stable* for $\mathcal Q\supseteq\mathcal I$ if it is internally stable and $a_i-(B\bar p)_i<0$ for $i\in\mathcal Q\setminus\mathcal I$. Linear asymptotic stability of $\bar p$ in $\mathbb R^N$ and in $\mathbb R^N_{\ge0}$ are equivalent to stability of the Jacobian. An equilibrium is *internally $D$-stable* if $-DB_{\mathcal I\mathcal I}$ is stable for every positive diagonal $D$ (guaranteed, e.g., by diagonal dominance or Volterra–Lyapunov stability).

**Theorem (exclusion).**
1. No two strictly stable communities differ by exactly one species.
2. If a community $\mathcal Q$ supports an internally $D$-stable equilibrium, no proper subcommunity of $\mathcal Q$ supports a different $\mathcal Q$-stable equilibrium.
3. If $-B_{\mathcal Q\mathcal Q}$ is Volterra–Lyapunov stable, there is a unique $\mathcal Q$-stable equilibrium supported in $\mathcal Q$, and it attracts every solution whose support is $\mathcal Q$.
4. If $B$ is $D$-symmetrizable and $\mathcal I$ supports a strictly stable equilibrium, no community containing or contained in $\mathcal I$ supports another strictly stable equilibrium.

**Corollary (Sperner bound).** Internally $D$-stable stable communities form an antichain under inclusion, so a Lotka–Volterra system on $N$ species has at most $\binom{N}{\lfloor N/2\rfloor}$ strictly stable, internally $D$-stable equilibria.

**Multiplicity.** The bound is nearly attainable: if each community in a family has weak internal competition ($\sum_{j\in\mathcal I,j\ne i}\hat B_{ij}\le\alpha a_i$) but strongly inhibits outsiders ($\sum_{j\in\mathcal I}\hat B_{ij}>a_i/(1-\alpha)$ for $i\notin\mathcal I$), with $\alpha<\frac12$, then every community in the family supports a strictly stable equilibrium. Without $D$-stability, a stable community can contain a stable single-species subcommunity.

## Expansion

If $\bar q$ is $D$-stable on $\mathcal Q$ and $\bar p\neq\bar q$ is supported inside $\mathcal Q$, then $x=\bar p-\bar q$ satisfies a sign condition incompatible with $\mathcal Q$-saturation of $\bar p$ by the Fiedler–Pták characterization of $P_0$ matrices (every nonzero $x$ has an index with $x_i\ne0$ and $x_i(Ax)_i\ge0$); $D$-stability of $-B_{\mathcal Q\mathcal Q}$ makes $B_{\mathcal Q\mathcal Q}$ a $P_0$ matrix. Sperner's lemma bounds the size of an antichain of subsets of an $N$-set. The results also apply to evolutionarily stable strategies through the replicator–Lotka–Volterra correspondence.

## Sources

- Won Eui Hong and Robert L. Pego, "Exclusion and multiplicity for stable communities in Lotka-Volterra systems", arXiv:2102.00611 (2021), Proposition 2.2, Theorems 3.1, 3.3 and 3.4, Corollaries 3.2, 3.10 and 4.3, Proposition 5.5 and Theorem 6.3, <https://doi.org/10.48550/arXiv.2102.00611>.
