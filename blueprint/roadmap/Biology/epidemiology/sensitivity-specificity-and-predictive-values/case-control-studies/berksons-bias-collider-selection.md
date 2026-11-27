# Berkson's bias under general admission probabilities

Berkson (1946) pointed out that two diseases that are independent in the general population may become spuriously associated in hospital-based studies, a bias with the structure of conditioning on a collider (Snoep et al. 2014). For admission probabilities of independent-causes form the association among admitted persons is negative: this is [the odds ratio among admitted persons, two diseases](../../../not-yet-classified/berkson-bias/hospital-odds-ratio.md) and [Berkson's inequality](../../../not-yet-classified/berkson-bias/hospital-frequency-lt.md). The following treats arbitrary admission probabilities. Let diseases $A$ and $B$ be independent in the population, with $P(A), P(B) \in (0, 1)$, and let hospital admission $H$ have conditional probabilities $h_{ab} = P(H \mid A = a, B = b) > 0$ for $a, b \in \{0, 1\}$. Then the odds ratio of $A$ and $B$ among the admitted is

$$\frac{h_{11}\, h_{00}}{h_{10}\, h_{01}},$$

so the sign of the induced association, that is, whether $P(A \mid B, H)$ is less than, equal to or greater than $P(A \mid \bar B, H)$, is the sign of $h_{11} h_{00} - h_{10} h_{01}$. Monotonicity of $h$ in each disease alone does not fix this sign: there are admission probabilities increasing in each disease for which the induced association is negative, zero or positive.

## Expansion

1. The model: two independent binary diseases and an admission indicator with conditional probabilities $h_{ab}$; collider conditioning for the graph $A \to H \leftarrow B$.
2. The conditional odds ratio $h_{11} h_{00}/(h_{10} h_{01})$ of $A$ and $B$ given $H$ under independence of $A$ and $B$, and the equivalence of its comparison with $1$ to the comparison of $P(A \mid B, H)$ with $P(A \mid \bar B, H)$.
3. Explicit monotone admission probabilities giving a negative, a zero and a positive induced association.
4. The historical debate and the causal reading of Berkson's examples, kept separate from the mathematics.

## Sources

- J. D. Snoep, A. Morabia, S. Hernández-Díaz, M. A. Hernán and J. P. Vandenbroucke, Commentary: A structural approach to Berkson's fallacy and a guide to a history of opinions about it, Int. J. Epidemiol. 43 (2014), 515–521. <https://doi.org/10.1093/ije/dyu026>
- Original result: J. Berkson, Limitations of the application of fourfold table analysis to hospital data, Biometrics Bull. 2 (1946), 47–53. <https://doi.org/10.2307/3002000> The spurious association of independent diseases in hospital data follows Snoep et al. (2014).
