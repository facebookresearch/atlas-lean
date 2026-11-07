# A subspace almost inside $A + A$ (Kelley–Meka)

There are real constants $C > 0$ and
$E > 0$ such that for every $n \in \mathbb{N}$, every set $A \subseteq \mathbb{F}_2^n$ and all real
numbers $\alpha$ and $\varepsilon$ with $\alpha > 0$, $0 < \varepsilon < 1$ and
$|A| / 2^n = \alpha$, there is an additive subgroup $V$ of $\mathbb{F}_2^n$ whose codimension
$\log_2(2^n / |V|)$ is at most $C \, (\log(\varepsilon^{-1} \alpha^{-1}) + 1)^E$ and which
satisfies $|V \cap (A + A)| \ge (1 - \varepsilon) |V|$. Here $A + A = \{a + b : a, b \in A\}$ and
$\log$ is the natural logarithm.

Kelley and Meka (Lemma 1.5 of arXiv:2302.05537) show that, over a finite field $\mathbb{F}_q$,
every set $A \subseteq \mathbb{F}_q^n$ of density at least $2^{-d}$ and every error parameter
$\tau$ admit a set $A' \subseteq A$ whose affine span $V + \theta$ has codimension
$O(d^5 \log(1/\tau)^4)$ and $|A' + A'| \ge (1 - \tau)|V + \theta|$, answering the question of
Hatami, Hosseini and Lovett. Over $\mathbb{F}_2$ the sumset $A' + A'$ lies in the subspace $V$,
which gives the statement. Bloom and Sisask improve this codimension bound (arXiv:2309.02353,
Theorem 3).

## Sources

- Zander Kelley and Raghu Meka, Strong bounds for 3-progressions, FOCS 2023, arXiv:2302.05537, https://arxiv.org/abs/2302.05537. Moved from `OpenConjectures/Combinatorics/AlmostSubspaceInSumset`.
