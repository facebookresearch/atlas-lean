# Isotropic plastic strain increment

For a real number $\mu$, the shear modulus, and real $3 \times 3$ matrices $\sigma_{\mathrm{trial}}$
and $\sigma$, the plastic strain increment is

$$\Delta\varepsilon_p = (2\mu)^{-1} (\sigma_{\mathrm{trial}} - \sigma).$$

With the convention $0^{-1} = 0$, $\Delta\varepsilon_p = 0$ when $\mu = 0$. In the model $\mu > 0$,
the stresses are tension positive and $\sigma$ is the stress returned by the
[return map](deviatoric-return.md); the strain is dimensionless.
