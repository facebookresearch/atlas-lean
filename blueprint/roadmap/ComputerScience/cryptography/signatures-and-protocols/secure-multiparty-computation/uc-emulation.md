# UC emulation

In Canetti's universally composable security framework, protocols run in the presence of an environment $E$, which chooses inputs and reads outputs and
has an input $z$, and an adversary that interacts with the protocol through its backdoor interface. Protocols, adversaries and environments are families indexed by a security parameter $\kappa$, and $\mathrm{Exec}(\pi, E, A, \kappa, z)$ is the output of $E$ on security parameter $\kappa$ and input $z$. A protocol $\pi$ *UC-emulates* a protocol $\phi$ if for every
adversary $A$ running in time polynomial in $\kappa$ there is such an adversary $S$ such that for every environment $E$ running in time polynomial in $\kappa$,
the ensembles $\{\mathrm{Exec}(\pi, E, A, \kappa, z)\}_{\kappa, z}$ and $\{\mathrm{Exec}(\phi, E, S, \kappa, z)\}_{\kappa, z}$ are indistinguishable as $\kappa \to \infty$.

In a quantitative form, $\pi$ UC-emulates $\phi$ with simulation overhead $\delta$ and emulation slack $\varepsilon$ if for every $A$ running in time $t_A$ there is $S$ running in
time $\delta\, t_A$ such that for every $E$ running in time $t_E$ and every $z$, the total variation distance between $\mathrm{Exec}(\pi, E, A, \kappa, z)$ and $\mathrm{Exec}(\phi, E, S, \kappa, z)$
is less than $\varepsilon(t_E)$. A protocol *UC-realizes* an ideal functionality $\mathcal{F}$ if it UC-emulates the ideal protocol for $\mathcal{F}$. It suffices to simulate the
dummy adversary, which only forwards messages between the environment and the backdoor interface.

## Sources

- R. Canetti, *Universally Composable Security: A Tutorial*, UC/EasyUC summer school, Boston University, 2025, <https://www.bu.edu/riscs/files/2025/08/Canetti.pdf>: the definitions of UC emulation (qualitative and quantitative) and ideal functionalities, and the dummy-adversary claim.
