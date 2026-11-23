# Existence and uniqueness of the Karlin–Altschul parameter

Let $A$ be a finite alphabet, $p$ a distribution on $A$ with $p_a > 0$ for every $a$, and $s$ a real score on $A \times A$ with $\sum_a \sum_b p_a p_b s_{ab} < 0$ and $s_{ab} > 0$ for some $a, b$. Then there is exactly one $\lambda > 0$ with $\Phi(\lambda) = 1$, where $\Phi$ is the [moment generating function](pair-mgf.md) (Karlin and Altschul 1990).

Equivalently, in the two-sequence form, write $\pi(a, b) = p_a p_b$ for the
[pair law](../sequence-alignment/two-sequence-karlin-altschul-statistics/pair-law.md) and
$\sigma(a, b) = s_{ab}$ for the
[pair score](../sequence-alignment/two-sequence-karlin-altschul-statistics/pair-score.md) of a letter
pair $(a, b) \in A \times A$. Then there is exactly one $\lambda > 0$ with
$\sum_{(a, b) \in A \times A} \pi(a, b)\, e^{\lambda \sigma(a, b)} = 1$, where the left side is the
[moment generating function](../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/score-mgf.md)
of the pair score under the pair law, that is $E\, e^{\lambda s_{XY}}$ for independent letters $X$
and $Y$ of law $p$. This sum over pairs equals the iterated sum $\Phi(\lambda)$.

## Sources

- S. Karlin and S. F. Altschul, *Methods for assessing the statistical significance of molecular sequence features by using general scoring schemes*, PNAS 87 (1990), 2264–2268.
