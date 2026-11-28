# Final size relation with arbitrary stage durations

Consider a newly invading infection in a closed, homogeneously mixing population of size $N$ with no demography, initially $S(0)$ susceptible people and a small number of infectious people. An individual infected at time $s$ has, at infection age $\tau \ge 0$, infectiousness $A(\tau) \ge 0$, so that the force of infection on each susceptible at time $t$ is

$$F(t) = \frac{1}{N} \int_{-\infty}^{t} A(t - s)\, \iota(s)\, ds, \qquad S'(t) = -F(t)\, S(t),$$

where $\iota(s) = -S'(s)$ is the incidence. The kernel $A$ may encode a latent stage, any number of distinct infectious stages and an isolation stage, each with an arbitrary integrable duration distribution, and may vary between individuals (for example super-spreaders) provided only its population average enters. The basic reproduction number is

$$R_0 = \int_0^\infty A(\tau)\, d\tau < \infty .$$

This is the age-of-infection (Kermack–McKendrick) model; writing the kernel as $a A$, with $a$ the rate of contacts sufficient to transmit and $A$ the mean infectivity at infection age, gives the same model with $R_0 = a \int_0^\infty A$.

**Theorem (final size relation).** With $S_\infty = \lim_{t \to \infty} S(t)$, and neglecting the initial infectives' contribution,

$$\ln \frac{S(0)}{S_\infty} = R_0 \, \frac{S(0) - S_\infty}{N} .$$

Equivalently, for an epidemic seeded at $t \to -\infty$ by a vanishing number of infectives with $S(t) \to S_0$ as $t \to -\infty$, the relation $\ln(S_0/S_\infty) = R_0 (S_0 - S_\infty)/N$ holds exactly. In particular, if $S(0) \approx N$ the attack fraction $Z = 1 - S_\infty / N$ satisfies

$$1 - Z = e^{-R_0 Z},$$

which has a unique root $Z \in (0, 1)$ if and only if $R_0 > 1$. The relation is identical to the one for the SIR model with exponentially distributed infectious periods: given $R_0$, the expected epidemic size does not depend on the distributions of latent and infectious periods. It can fail under heterogeneous mixing (for example a core group, as for sexually transmitted infections), although it persists for a general class of spatial contact structures.

## Depends on

- [Final-size equation (Kermack–McKendrick 1927)](../../kermack-mckendrick-sir-model/final-size-eq.md)

## Expansion

Divide $S' = -F S$ by $S$ and integrate over $[0, \infty)$: $\ln(S(0)/S_\infty) = \int_0^\infty F(t)\, dt$. Exchanging the order of integration in $\int_0^\infty \int A(t - s)\, \iota(s)\, ds\, dt$ gives $R_0 \int \iota(s)\, ds / N = R_0 (S(0) - S_\infty)/N$, since each infection contributes its total infectiousness $\int A = R_0$ once, regardless of how that infectiousness is spread over time. Stage structure and duration distributions only reshape $A$, not its integral; with $A(\tau) = \beta e^{-\gamma \tau}$ the model is the SIR model with $R_0 = \beta/\gamma$. For the exact form, integrate over the whole real line instead, using Fubini as above. The uniqueness statement follows from the concavity of $Z \mapsto 1 - e^{-R_0 Z}$, whose slope at $0$ is $R_0$. The practical consequence emphasized by Ma and Earn is that, for an emerging respiratory pathogen, the expected magnitude of the epidemic can be estimated as soon as $R_0$ can be approximated, and improves only with better estimates of $R_0$.

## Sources

- J. Ma and D. J. D. Earn, "Generality of the final size formula for an epidemic of a newly invading infectious disease", Bulletin of Mathematical Biology 68 (2006), 679–702, abstract and main results, <https://doi.org/10.1007/s11538-005-9047-7> (PMC7088645).
- Brauer F. Mathematical epidemiology: past, present, and future. *Infectious Disease Modelling* 2:113–127 (2017), Section 5.1, "The infection age epidemic model", equations (4) and (5), <https://doi.org/10.1016/j.idm.2017.02.001> (PMC6001967).
- W. O. Kermack and A. G. McKendrick, "A contribution to the mathematical theory of epidemics", Proceedings of the Royal Society of London A 115 (1927), 700–721, <https://doi.org/10.1098/rspa.1927.0118>.
