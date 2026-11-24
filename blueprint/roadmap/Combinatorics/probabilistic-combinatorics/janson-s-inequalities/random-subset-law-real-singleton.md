# Probability that a random subset equals a given subset

Let $\alpha$ be a finite set and $p \colon \alpha \to [0, 1]$, and let $R \subseteq \alpha$ be the random subset that contains each element $a$ independently with probability $p(a)$, a subset being identified with its indicator $b \colon \alpha \to \{\text{true}, \text{false}\}$. For every indicator $b$,

$$\Pr[R = b] = \prod_{a \in \alpha} \begin{cases} p(a) & \text{if } b(a) = \text{true}, \\ 1 - p(a) & \text{if } b(a) = \text{false}. \end{cases}$$

Equivalently, for every $T \subseteq \alpha$, $\Pr[R = T] = \prod_{a \in T} p(a) \prod_{a \in \alpha \setminus T} (1 - p(a))$.

## Sources

- Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes, Spring 2019, Setup 7.10, https://yufeizhao.com/pm/sp19/pmnotes.pdf.
