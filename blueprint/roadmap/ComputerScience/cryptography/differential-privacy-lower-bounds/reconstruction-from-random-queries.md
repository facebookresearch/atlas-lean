# Reconstruction from linearly many random $\pm 1$ queries

Let a database hold one secret sign $d_i \in \{\pm 1\}$ per row, $i \in [n]$, and let a $\pm 1$ query $v \in \{\pm1\}^n$ ask for $\langle v, d\rangle$. For every $\eta > 0$ and every error bound $\alpha = \alpha(n)$ there is a constant $b$ and an attack using $bn$ uniformly random $\pm 1$ queries that, whenever the curator answers at least a $\tfrac12 + \eta$ fraction of the queries within absolute error $\alpha$, outputs a database $c \in \{\pm 1\}^n$ agreeing with $d$ in all but at most $(2\alpha/\eta)^2$ entries; the attack outputs any $c$ consistent within $\alpha$ with a $\tfrac12 + \eta$ fraction of the answers, and it fails only with probability exponentially small in $n$ over the choice of queries (Dwork and Roth, Theorem 8.2 and its proof). Hence answering $O(n)$ random $\pm 1$ queries with error $o(\sqrt n)$ is blatantly non-private.

## Proof sketch

The true database and the output both fit a $\tfrac12 + \eta$ fraction of the answers, so their difference $z \in \{-2, 0, 2\}^n$ satisfies $|\langle v_j, z\rangle| \le 2\alpha$ for at least a $2\eta$ fraction of the queries. If $z$ has at least $(2\alpha/\eta)^2$ nonzero entries, anti-concentration of a sum of independent $\pm 2$ values bounds the probability of this for one query by $\eta$; a Chernoff bound and a union bound over the at most $3^n$ vectors $z$ finish the proof once $b > 4\ln 3/\eta$. The attack is not efficient; polynomial-time reconstruction, which Dwork and Roth (§8.3) attribute to Dwork, McSherry and Talwar, is not covered by this statement.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)
- [Dinur–Nissim reconstruction attack](../differential-privacy/dinurnissim-reconstruction-attack.md)

## Sources

- Cynthia Dwork and Aaron Roth, "The Algorithmic Foundations of Differential Privacy", Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, §8.1, Theorem 8.2.
