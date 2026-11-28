# Allometric size scaling with sigmoid maturation

**Allometric law.** A pharmacokinetic parameter $y$ (a clearance or a compartment volume) is scaled to a size descriptor $x > 0$ (total body weight, fat-free mass, or a volume itself) by

$$y = b\,x^{a},$$

with a constant $b > 0$ and an exponent $a$, commonly $a = 0.75$ for clearances. Referenced to a standard patient with size $x_{\mathrm{ref}}$ and parameter $y_{\mathrm{ref}}$, this is $y = y_{\mathrm{ref}}\,(x/x_{\mathrm{ref}})^{a}$.

**Sigmoid maturation.** For a covariate $x \ge 0$ (postmenstrual age, or postnatal age plus 40 weeks), a half-maturation value $E_{50} > 0$ and a steepness $\lambda > 0$,

$$f_{\mathrm{sigmoid}}(x; E_{50}, \lambda) = \frac{x^{\lambda}}{x^{\lambda} + E_{50}^{\lambda}} ,$$

which increases from $0$ to $1$, equals $1/2$ at $x = E_{50}$, and multiplies the metabolic clearance of immature patients. Normalizing by its value at the reference patient keeps $y = y_{\mathrm{ref}}$ there.

**Combined clearance model.** A clearance takes the form

$$\mathrm{CL} = \theta_{\mathrm{CL}}\Big(\frac{x}{x_{\mathrm{ref}}}\Big)^{0.75}\,\frac{f_{\mathrm{sigmoid}}(\mathrm{PMA}; E_{50}, \lambda)}{f_{\mathrm{sigmoid}}(\mathrm{PMA}_{\mathrm{ref}}; E_{50}, \lambda)}\;\cdot\; g(\text{other covariates}),$$

with $g$ collecting age-decline factors $f_{\mathrm{aging}}(\kappa) = e^{\kappa(\mathrm{AGE} - \mathrm{AGE}_{\mathrm{ref}})}$ and comedication effects. In the general-purpose propofol model the metabolic-clearance maturation uses $E_{50} = 42.3$ weeks and $\lambda = 9.06$ in postmenstrual age, and the central volume follows an $E_{\max}$ function of weight, $f_{\mathrm{sigmoid}}(\mathrm{WGT}; 33.6, 1)$.

## Expansion

Linear scaling to body weight is adequate for intermediate sizes but over-predicts clearance in large and under-predicts it in small patients; the sublinear exponent $0.75$, observed across species, corrects both ends. Maturation of hepatic enzymes is an additional, size-independent process: with the same allometric exponent at all ages, the Hill-type factor $f_{\mathrm{sigmoid}}$ captures the low clearance of neonates and saturates to $1$ in children and adults. An $E_{\max}$ dependence of the central volume on weight ($\lambda = 1$) implies relatively larger per-kilogram induction doses for low-weight patients and smaller ones for obese patients. These scaled parameters are the volumes and clearances of a three-compartment model with an effect site.

## Sources

- M. M. Sahinovic, M. M. R. F. Struys and A. R. Absalom, "Clinical pharmacokinetics and pharmacodynamics of propofol", Clinical Pharmacokinetics 57 (2018), section "Compartmental Modelling" and Table 2 (Eleveld model equations), <https://doi.org/10.1007/s40262-018-0672-3> (PMC6267518).
- D. J. Eleveld, P. Colin, A. R. Absalom and M. M. R. F. Struys, "Pharmacokinetic–pharmacodynamic model for propofol for broad application in anaesthesia and sedation", British Journal of Anaesthesia 120 (2018).
