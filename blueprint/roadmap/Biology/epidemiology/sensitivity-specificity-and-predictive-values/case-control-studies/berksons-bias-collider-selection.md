# Berkson's bias from hospital selection

Berkson (1946) pointed out that two diseases that are independent in the general population may become spuriously associated in hospital-based studies; in his example the diseases were independent in the source population and the probabilities of hospitalization for each disease were independent, yet the diseases were associated among hospitalized individuals, a bias with the structure of conditioning on a collider (Snoep et al. 2014). The following makes this exact. Let diseases $A$ and $B$ be independent in the population, with $P(A), P(B) \in (0, 1)$, and let hospital admission $H$ have the independent-causes form

$$P(\bar H \mid A = a, B = b) = q_0\, q_A^{a}\, q_B^{b}, \qquad a, b \in \{0, 1\},$$

with $q_0, q_A, q_B \in (0, 1)$: the background and each disease independently fail to lead to admission. Writing $h_{ab} = P(H \mid a, b)$, independence of $A$ and $B$ gives the odds ratio of $A$ and $B$ among the admitted as $h_{11} h_{00}/(h_{10} h_{01})$, and here

$$h_{11} h_{00} - h_{10} h_{01} = (1 - q_0 q_A q_B)(1 - q_0) - (1 - q_0 q_A)(1 - q_0 q_B) = -q_0 (1 - q_A)(1 - q_B) < 0,$$

so among admitted persons the diseases are negatively associated: $P(A \mid B, H) < P(A \mid \bar B, H)$. For general admission probabilities $h_{ab} > 0$ the sign of the induced association is the sign of $h_{11} h_{00} - h_{10} h_{01}$, and monotonicity of $h$ in each disease alone does not fix it.

## Expansion

1. The model: two independent binary diseases and an admission indicator with conditional probabilities $h_{ab}$; collider conditioning for the graph $A \to H \leftarrow B$.
2. The conditional odds ratio $h_{11} h_{00}/(h_{10} h_{01})$ of $A$ and $B$ given $H$ under independence of $A$ and $B$.
3. The independent-causes computation and the negative association.
4. A counterexample showing that monotone $h$ alone allows a positive or zero induced association.
5. The historical debate and the causal reading of Berkson's examples, kept separate from the mathematics.

## Sources

- J. D. Snoep, A. Morabia, S. Hernández-Díaz, M. A. Hernán and J. P. Vandenbroucke, Commentary: A structural approach to Berkson's fallacy and a guide to a history of opinions about it, Int. J. Epidemiol. 43 (2014), 515–521. <https://doi.org/10.1093/ije/dyu026>
- Original result: J. Berkson, Limitations of the application of fourfold table analysis to hospital data, Biometrics Bull. 2 (1946), 47–53. <https://doi.org/10.2307/3002000> The spurious association of independent diseases in hospital data follows Snoep et al. (2014).
