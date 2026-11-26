# Online play is unchanged by flipping the current sign

Let $A$ be a deterministic online algorithm, $\sigma : \mathrm{Fin}\,T \to \{\text{true},\text{false}\}$ a sign sequence and $t$ a round. Let $\sigma^{(t)}$ be $\sigma$ with its $t$-th coordinate negated. Then the play at round $t$ is the same for both sequences:

$$A_t(\sigma^{(t)}_0, \dots, \sigma^{(t)}_{t-1}) = A_t(\sigma_0, \dots, \sigma_{t-1}),$$

because the play at round $t$ reads only the coordinates before $t$.
