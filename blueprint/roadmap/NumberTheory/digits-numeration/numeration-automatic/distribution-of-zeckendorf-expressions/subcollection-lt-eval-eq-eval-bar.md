# Reduction lemma for counting a subcollection

Let $E \subseteq \tilde E$ be Zeckendorf
collections, and let $\tilde H$ be a strictly increasing sequence of positive integers such that
$\varepsilon \mapsto \sum_k \varepsilon_k \tilde H_k$ is a bijection from $\tilde E$ onto
$\mathbb{N}$. For a natural number $x$ let $R(x)$ be the set of natural numbers $n < x$ of the
form $n = \sum_k \varepsilon_k \tilde H_k$ with $\varepsilon \in E$. Let $\mu \in \tilde E$ be
nonzero, suppose that $\mu$ has an immediate predecessor $\check\mu$ in $E$ (the largest element
of $E$ that is $\lt _a \mu$ in the ascending lexicographic order), and suppose that $\check\mu$ has
an immediate successor $\bar\mu$ in $E$ (the smallest element of $E$ that is $>_a \check\mu$).
Then $R(\sum_k \mu_k \tilde H_k) = R(\sum_k \bar\mu_k \tilde H_k)$.

## Sources

- Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25, Lemma 7 (`integers-2025-A25-lem-7`; arXiv:2308.12872v1, Section 3.2, with the paper's definition of `μ̌` and `μ̄` there).
