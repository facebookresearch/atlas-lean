# Optimal switching time for traveler testing in a two-country SIR model

**Model.** Two countries $i \in \{1,2\}$ have SIR compartments $S_i, I_i, R_i$, transmission rates $\beta_i$, recovery rates $\gamma_i$, and travel weights $w^S_{ij}, w^I_{ij}$ (fractions of susceptible and infected residents of $i$ present in $j$, each row summing to one). Country $i$ tests incoming travelers at rate $u_i(t) \in [0,1]$, and an infected visitor who is not caught by the destination's testing can infect locals there. For country 1,

$$ \dot S_1 = -S_1 \Bigl( w^S_{11} \beta_1 (1 - u_1) w^I_{21} I_2 + w^S_{12} \beta_2 w^I_{22} I_2 + w^S_{11} \beta_1 w^I_{11} I_1 \Bigr), \qquad \dot I_1 = -\dot S_1 - \gamma_1 I_1, \qquad \dot R_1 = \gamma_1 I_1, $$

and symmetrically for country 2 with its fixed testing policy $u_2$. Country 1 chooses a measurable $u_1 : [0,T] \to [0,1]$ to minimize testing costs, the economic loss from rejecting infected tourists, and terminal mortality:

$$ \mathcal{J}(u_1) = \int_0^T u_1(t) \bigl( c_{test} N_2 + c_t I_2(t) \bigr) w_{21}\, dt + c_d d_R R_1(T) + c_d d_I I_1(T). $$

**Structure of the optimal control.** The Hamiltonian is linear in $u_1$, so by Pontryagin's principle an optimal control equals $1$ where the switching function

$$ \phi(t) = (\lambda_1^1 - \lambda_1^2) S_1(t) w^S_{11} \beta_1 w^I_{21} I_2(t) + c_{test} N_2 w_{21} + c_t I_2(t) w_{21} $$

is negative and $0$ where it is positive, with adjoint terminal data $\lambda_1^2(T) = c_d d_I$, $\lambda_1^1(T) = 0$; away from singular arcs ($\phi \equiv 0$ on an interval) the optimal testing policy is bang-bang. Since $\phi(T) = -c_d d_I S_1(T) w^S_{11} \beta_1 w^I_{21} I_2(T) + (c_{test} N_2 + c_t I_2(T)) w_{21}$, testing remains optimal near the horizon unless the epidemic in country 2 is nearly over.

**Theorem 3.1 (single switch on).** Among controls $u_1 = \mathbf{1}_{[t^*, T]}$ (start testing at $t^*$), an interior optimal switching time $t^* \in (0,T)$ satisfies

$$ S_1(t^*) = \frac{c_{test} N_2 w_{21} + c_t I_2(t^*) w_{21}}{c_d d_I w^S_{11} \beta_1 w^I_{21} I_2(t^*) + c_d d_R \gamma_1 w^S_{11} \beta_1 w^I_{21} I_2(t^*)\, (T - t^*)}. $$

The same implicit equation characterizes the optimal switch for controls that stop testing at $t^*$ (Theorem 3.2) and, at each switching time, for controls testing on an interval $[t_1, t_2]$ (Theorem 3.3).

## Expansion

For a piecewise constant control, $\mathcal{J}$ becomes a function of the switching time, and $\frac{d\mathcal{J}}{dt^*} = 0$ balances two effects of moving the switch: the marginal running cost $(c_{test} N_2 + c_t I_2(t^*)) w_{21}$ of testing at $t^*$, against the marginal infections averted in country 1, $S_1(t^*) w^S_{11} \beta_1 w^I_{21} I_2(t^*)$, valued at the mortality cost of an infection that is either still infectious at $T$ ($c_d d_I$) or has recovered over the remaining time ($c_d d_R \gamma_1 (T - t^*)$, to first order). Solving the balance for $S_1(t^*)$ gives the implicit equation, which is evaluated numerically along the trajectory.

## Sources

- Maria Teresa Chiri, Christopher Denaro, Xiaoqian Gong, Benedetto Piccoli, "Optimal Control of Traveler Testing in Epidemic Models", arXiv (2026). Section 2.1 (multi-region SIR model with visitor transmission), Section 3.1 (Hamiltonian, switching function, adjoint system), Section 3.2 (Theorems 3.1-3.3). <https://doi.org/10.48550/arXiv.2609.25372>
