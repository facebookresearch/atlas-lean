# Oscillation criterion for cyclic repressor rings

**Model.** A ring of $n$ genes in which the protein $P_{i-1}$ represses transcription of gene $G_i$ (indices modulo $n$, so $P_0 = P_n$) is described, after the quasi-steady-state approximation of promoter binding, by the $2n$ ordinary differential equations

$$\dot r_i = -(a_i + \mu)\, r_i + \beta_i\, g\, \frac{K_{i-1}^{\nu_i}}{K_{i-1}^{\nu_i} + p_{i-1}^{\nu_i}}, \qquad \dot p_i = -(b_i + \mu)\, p_i + c_i\, r_i, \qquad i = 1, \dots, n,$$

where $r_i, p_i \ge 0$ are the mRNA and protein concentrations, $a_i, b_i > 0$ their degradation rates, $c_i > 0$ the translation rate, $\beta_i > 0$ the transcription rate per unit template, $g > 0$ the template (plasmid) concentration, $K_{i-1} > 0$ and $\nu_i > 0$ the repression threshold and Hill coefficient of $P_{i-1}$ on the promoter of $G_i$, and $\mu > 0$ a common dilution rate (dilution time $T_d = \ln 2 / \mu$).

**Negative ring.** Take $n$ odd, so that the single feedback loop, which contains $n$ repressions, is negative.

**Instability implies oscillation.** The system has a unique equilibrium, and the protein concentrations $p_1, \dots, p_n$ show stable oscillations whenever the Jacobian matrix at that equilibrium has an eigenvalue in the open right half-plane.

**Explicit criterion (homogeneous ring).** Suppose all parameters are independent of $i$: $a_i = a$, $b_i = b$, $c_i = c$, $\beta_i = \beta$, $K_i = K$, $\nu_i = \nu$, and write $d$ for the dilution rate $\mu$. Define

$$Q = \frac{\sqrt{(a+d)(b+d)}}{(a+b+2d)/2} \in (0, 1], \qquad W(n, Q) = \frac{2\left(-\cos\frac{\pi}{n} + \sqrt{\cos^2\frac{\pi}{n} + Q^2 \sin^2\frac{\pi}{n}}\right)}{Q^2 \sin^2\frac{\pi}{n}}.$$

Then the proteins oscillate if both

$$\nu > W(n, Q) \qquad \text{and} \qquad c\beta g > \left(\frac{W(n,Q)}{\nu - W(n,Q)}\right)^{1/\nu} \frac{\nu}{\nu - W(n,Q)}\, K\, (a+d)(b+d)$$

hold.

## Expansion

The first inequality says the Hill coefficient must exceed a threshold that depends only on the ring length and on the ratio $Q$ of the geometric to the arithmetic mean of the two total decay rates $a+d$ and $b+d$; the second says the maximal production gain $c\beta g$ must beat the product of the decay rates by a factor fixed by $\nu$ and $W$. Both are sufficient conditions for the linearization at the unique equilibrium to have an unstable eigenvalue, after which the instability-implies-oscillation statement gives a periodic orbit. With equal decay rates ($a = b$, so $Q = 1$) the threshold is $W(n,1) = 2/(1 + \cos(\pi/n))$, which for $n = 3$ is $4/3$.

On units: $\beta$ is a rate per unit template concentration, so the maximal transcription rate is $\beta g$ (the transcription term of the model) and the threshold is on $c\beta g$; the source's Eq. (10) writes $c\beta$, with the template concentration absorbed into $\beta$.

For the repressilator with $n = 3$, mRNA half-life $8$ min, protein half-life $90$ min, $\beta = 0.4$, $c = 0.5$, $K = 5$ nM and $\nu = 2$, the first inequality holds for every dilution time $T_d$ between $5$ and $80$ min, and the second inequality traces the region of transcription and translation rates that support oscillations as $T_d$ varies. Weakening one repressor (raising its threshold $K$, as in an operator point mutation) shrinks the range of dilution times with an unstable equilibrium, matching the narrower oscillatory range observed in a cell-free microfluidic reactor. Simulated periods grow monotonically with $T_d$, and $5$-node rings oscillate with longer periods than $3$-node rings, as measured.

## Depends on

- [Parity dichotomy of cyclic repressor rings](parity-dichotomy-of-cyclic-repressor-rings.md)

## Sources

- H. Niederholtmeyer, Z. Z. Sun, Y. Hori, E. Yeung, A. Verpoorte, R. M. Murray, S. J. Maerkl, "Rapid cell-free forward engineering of novel genetic ring oscillators", eLife 4 (2015) e09771, Materials and methods, section "Model": Equation 6 (the ring model), Equation 7 (dilution time), Equations 9 and 10 with the definitions of $W(n,Q)$ and $Q$ (oscillation conditions, quoted from Theorem 3 of Hori, Kim and Hara 2011), Table 2 (parameters), and Figure 2, figure supplements 1 and 3 and Figure 3F (parameter regions and periods), <https://doi.org/10.7554/eLife.09771>, PMCID PMC4714972.
