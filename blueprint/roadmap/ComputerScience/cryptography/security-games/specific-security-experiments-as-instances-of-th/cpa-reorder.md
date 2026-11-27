# Reordering the CPA sample space

For each $q$, the explicit equivalence

$$
\mathrm{Bool} \times K \times R \times X \times X^q \;\simeq\; K \times X^q \times X \times \mathrm{Bool} \times R
$$

whose forward map sends $(b, k, r, r_s, \rho)$ to $(k, \rho, r_s, b, r)$. Its inverse puts the challenge bit first: it sends $(k, \rho, r_s, b, r)$ to $(b, k, r, r_s, \rho)$. It relates the sample order of the Framework CPA game (bit, key, coins, challenge randomness, tape) to that of the PRF file's game (key, tape, challenge randomness, bit, coins).
