# Hellinger perturbation bound for posteriors

On any measurable space with a σ-finite prior $\mu_0$, let $\Phi_1$, $\Phi_2$, $M_1$, $M_2$ be measurable functions with

$$
\Phi_i \ge -M_1, \qquad |\Phi_1 - \Phi_2| \le M_2 \, \delta,
$$

let $w = e^{M_1}(1 + M_2^2)$ be $\mu_0$-integrable with $\int w \, d\mu_0 \le W$, and let both normalising
constants be at least $z > 0$. Then the posteriors $\mu_i \propto e^{-\Phi_i} \mu_0$ satisfy

$$
d_{\mathrm{Hell}}(\mu_1, \mu_2) \le |\delta| \, \sqrt{\frac{W}{4z} + \frac{W^2}{2z^2}} .
$$

This is the common estimate inside the proofs of the well-posedness and approximation theorems,
with an explicit constant: $|Z_1 - Z_2| \le |\delta| W$, and $2 d_{\mathrm{Hell}}^2$ splits into a term
controlled by $|e^{-\Phi_1/2} - e^{-\Phi_2/2}| \le \tfrac12 e^{M_1/2} |\Phi_1 - \Phi_2|$ and a term
controlled by $|Z_1^{-1/2} - Z_2^{-1/2}|$. No topology or dimension is involved; the dimension enters
only through the lower bound on the normalising constants.

## Sources

- Masoumeh Dashti and Andrew M. Stuart, *The Bayesian approach to inverse problems*, in *Handbook of Uncertainty Quantification*, Springer (2017), 311–428, DOI 10.1007/978-3-319-12385-1_7; numbering of arXiv:1302.6989v4 (2015), proofs of Theorems 4.5 and 4.9.
