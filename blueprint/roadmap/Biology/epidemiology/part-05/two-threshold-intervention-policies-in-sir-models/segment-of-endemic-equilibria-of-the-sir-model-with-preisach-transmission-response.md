# Segment of endemic equilibria of the SIR model with Preisach transmission response

**Model.** Different groups of susceptible individuals follow an intervention with different start and stop thresholds. Let a relay $\mathcal R_\alpha$ with thresholds $\alpha=(\alpha_1,\alpha_2)$, $0\le\alpha_1<\alpha_2\le1$, switch to state $1$ when the infected density $I(t)$ reaches $\alpha_2$ and back to $0$ when it falls to $\alpha_1$. The population-averaged basic reproduction number is then given by a continuous Preisach operator,

$$R_0(t)=R_0^{nat}-(R_0^{nat}-R_0^{int})\iint_\Pi q(\alpha)\,\bigl(\mathcal R_\alpha[r^0_\alpha]I\bigr)(t)\,d\alpha_1\,d\alpha_2,\qquad \Pi=\{0\le\alpha_1<\alpha_2\le1\},$$

where $q>0$ is a bounded probability density on $\Pi$ and $R_0^{nat}>R_0^{int}>1$. This feeds into the normalized SIR system $\dot I=R_0SI-I$, $\dot S=-R_0SI-\rho S+\rho$ with $0<\rho<1$. Let $E_{nat}$ and $E_{int}$ be the endemic equilibria of the system with constant $R_0=R_0^{nat}$ and $R_0=R_0^{int}$.

**Proposition.**

1. (Continuum of equilibria.) The infection-free state $(0,1)$, with all relays off, is the unique infection-free equilibrium. The endemic equilibria

$$E_\theta=\Bigl(\bigl(1-\tfrac1{R_0^\theta}\bigr)\rho,\ \tfrac1{R_0^\theta}\Bigr)$$

form a non-degenerate line segment $E_0E_1$ that lies in the interior of the segment $E_{int}E_{nat}$. Each value $R_0^\theta$ is compatible with some admissible frozen relay configuration.
2. (Homogeneous limit.) Let the densities $q(\cdot;\sigma)$ converge to the Dirac mass at $(I_{nat},I_{int})$ as $\sigma\to0$, with $0<I_{nat}<I_{int}<1$, and let $E^\sigma_0E^\sigma_1$ be the corresponding segments of equilibria. Then:
   - if $E_{int}E_{nat}$ lies to the left of the line $I=I_{nat}$, both endpoints tend to $E_{nat}$;
   - if $E_{int}E_{nat}$ lies to the right of the line $I=I_{int}$, both endpoints tend to $E_{int}$;
   - if $E_{int}E_{nat}$ meets the band $\{I_{nat}\le I\le I_{int}\}$, the segment $E^\sigma_0E^\sigma_1$ tends to the part of $E_{int}E_{nat}$ inside that band.

So heterogeneity of the response replaces the isolated equilibria, and the periodic attractor of the single-switch model, with a whole segment of equilibria. Which equilibrium is reached depends on the history of the epidemic.

## Expansion

At equilibrium $I=I^*$ is constant, so every relay with $\alpha_2\le I^*$ is on and every relay with $\alpha_1\ge I^*$ is off. Relays with $\alpha_1<I^*<\alpha_2$ may be in either state, and that freedom produces a continuum of possible values $R_0$. Imposing $I^*=(1-1/R_0)\rho$ gives a scalar consistency condition. Its extreme solutions, with all undetermined relays off or all on, give the two endpoints. Both lie strictly between $E_{int}$ and $E_{nat}$ because $q>0$ and both groups of relays carry positive mass. As $q$ concentrates at a point, the undetermined set shrinks to the band between the two thresholds, which recovers the single-switch alternatives.

## Depends on

- [Endemic equilibria of the SIR model with a two-threshold intervention switch](endemic-equilibria-of-the-sir-model-with-a-two-threshold-intervention-switch.md)

## Sources

- Dmitrii Rachinskii, Samiha Rouf, "Dynamics of SIR model with heterogeneous response to intervention policy", arXiv:2103.07989 (2021), Section 3 (Preisach model of heterogeneous transmission), Propositions 2 and 3, <https://doi.org/10.48550/arXiv.2103.07989>.
