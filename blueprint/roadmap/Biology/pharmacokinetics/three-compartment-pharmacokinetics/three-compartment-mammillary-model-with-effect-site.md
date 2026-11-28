# Three-compartment mammillary model with an effect site

**Model.** A central compartment of volume $V_1$ exchanges drug with a fast peripheral compartment ($V_2$) and a slow peripheral compartment ($V_3$) through intercompartmental clearances $Q_2, Q_3$, and eliminates it with clearance $\mathrm{CL}$. With amounts $A_1, A_2, A_3 \ge 0$, concentrations $C_i = A_i/V_i$, and infusion rate $u(t) \ge 0$ into the central compartment,

$$\begin{aligned}
\dot A_1 &= u(t) - \mathrm{CL}\,C_1 - Q_2\,(C_1 - C_2) - Q_3\,(C_1 - C_3),\\
\dot A_2 &= Q_2\,(C_1 - C_2),\\
\dot A_3 &= Q_3\,(C_1 - C_3).
\end{aligned}$$

The effect-site concentration $C_e$ lags the plasma concentration $C_p = C_1$ through

$$\dot C_e = k_{e0}\,(C_p - C_e), \qquad k_{e0} > 0,$$

and the drug effect is a Hill function of $C_e$.

**Properties.**

1. The system is linear with nonnegative off-diagonal coupling, so nonnegative inputs and initial amounts give nonnegative amounts, and $\frac{d}{dt}(A_1 + A_2 + A_3) = u - \mathrm{CL}\,C_1$.
2. After a bolus, $C_p(t) = \sum_{j=1}^{3} c_j e^{-\lambda_j t}$ with $\lambda_1 > \lambda_2 > \lambda_3 > 0$ the negatives of the eigenvalues of the rate matrix, giving the rapid distribution, slow distribution and terminal elimination phases.
3. The plasma–effect-site equilibration half-time is $t_{1/2}^{k_{e0}} = \ln 2/k_{e0}$; for the hypnotic effect of propofol it is about $2.5$ minutes, independent of age, whereas the haemodynamic effect equilibrates more slowly (about $5$ minutes in young and up to $10$ minutes in elderly patients).
4. Target-controlled infusion inverts the model: given a target $C_p$ or $C_e$ trajectory, $u(t)$ is computed from the model so that the predicted concentration follows the target.

## Depends on

- [Effect-compartment concentration](../pharmacodynamic-response-models/effect-conc.md)
- [Baseline-plus-increment Hill response](../pharmacodynamic-response-models/response.md)

## Expansion

In terms of microconstants $k_{10} = \mathrm{CL}/V_1$, $k_{12} = Q_2/V_1$, $k_{21} = Q_2/V_2$, $k_{13} = Q_3/V_1$, $k_{31} = Q_3/V_3$ the amounts satisfy $\dot A = M A + u\,e_1$ with a compartmental matrix $M$ whose columns sum to $-k_{10}, 0, 0$; such matrices are Metzler with strictly negative eigenvalues when $k_{10} > 0$ and the graph is connected, which gives property 2. The effect compartment carries negligible mass, so it does not feed back on the plasma kinetics; its solution is the convolution of $C_p$ with $k_{e0}e^{-k_{e0}t}$. Propofol models differ in how $V_1, V_2, V_3, \mathrm{CL}, Q_2, Q_3$ scale with covariates (size, age, sex, comedication); see [allometric size scaling with sigmoid maturation](../allometric-scaling-of-pharmacokinetic-parameters/allometric-size-scaling-with-sigmoid-maturation.md).

## Sources

- M. M. Sahinovic, M. M. R. F. Struys and A. R. Absalom, "Clinical pharmacokinetics and pharmacodynamics of propofol", Clinical Pharmacokinetics 57 (2018), section "Compartmental Modelling" with Fig. 2 (three-compartment PK/PD model) and section "Pharmacodynamics (PD)" (plasma–effect-site equilibration half-times), <https://doi.org/10.1007/s40262-018-0672-3> (PMC6267518).
