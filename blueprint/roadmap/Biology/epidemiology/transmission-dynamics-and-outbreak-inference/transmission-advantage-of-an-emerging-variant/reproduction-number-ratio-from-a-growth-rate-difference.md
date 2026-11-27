# Reproduction-number ratio from a growth-rate difference

Let a resident variant and a new variant grow exponentially at rates $r_1$ and $r_2 = r_1 + \Delta r$, and assume both share the same generation-interval distribution $g$. By the Euler–Lotka relation each reproduction number is $R_v = 1 / M_g(-r_v)$ with $M_g(-r) = \int e^{-ra}\, g(da)$, so the multiplicative transmission advantage is

$$\frac{R_2}{R_1} = \frac{M_g(-r_1)}{M_g(-r_2)} .$$

Special cases:

- **Fixed generation interval** $g = \delta_T$: $R_2 / R_1 = e^{\Delta r\, T}$, independent of $r_1$.
- **Gamma generation interval** with shape $\alpha > 0$ and rate $\beta > 0$ (mean $T = \alpha/\beta$), for $r_1, r_2 > -\beta$:

$$\frac{R_2}{R_1} = \left(\frac{1 + r_2/\beta}{1 + r_1/\beta}\right)^{\alpha} = \exp\!\left(\alpha \log\frac{\beta + r_2}{\beta + r_1}\right),$$

whose exponent is $\alpha \log\frac{\beta + r_2}{\beta + r_1} = \Delta r\, T\,\bigl(1 + O((|r_1| + |\Delta r|)/\beta)\bigr)$ as $(|r_1| + |\Delta r|)/\beta \to 0$; the fixed-interval formula is therefore a good approximation when growth rates are small compared with $\beta$.

For a fixed generation interval the ratio depends on the growth rates only through $\Delta r$. In general it depends on both rates: in the gamma case the ratio is $\bigl(1 + \Delta r/(\beta + r_1)\bigr)^{\alpha}$, which changes with $r_1$ for fixed $\Delta r \ne 0$. If the new variant instead had a shorter generation interval, the same $\Delta r$ would be compatible with a smaller (or no) increase in $R$.

## Depends on

- [Reproductive number from growth rate and generation interval](../../euler-lotka-equation-and-the-reproduction-number/reproduction-number.md)
- [Fixed generation interval](../../euler-lotka-equation-and-the-reproduction-number/reproduction-number-dirac.md)
- [Gamma generation interval](../../euler-lotka-equation-and-the-reproduction-number/reproduction-number-gamma-measure.md)

## Proof sketch

For the Dirac interval $R_v = e^{r_v T}$, so the ratio is $e^{(r_2 - r_1)T}$. For the gamma interval $R_v = (1 + r_v/\beta)^{\alpha}$, giving the stated quotient; writing $\log\frac{\beta + r_2}{\beta + r_1} = \log\!\left(1 + \frac{\Delta r}{\beta + r_1}\right) = \frac{\Delta r}{\beta + r_1}\,(1 + O(|\Delta r|/\beta))$ and $\alpha/(\beta + r_1) = T\,(1 + O(|r_1|/\beta))$ gives the approximation. With a mean generation interval of $5.5$ days, the estimated advantage $\Delta r \approx 0.104$ per day for lineage B.1.1.7 corresponds to $e^{0.104 \times 5.5} \approx 1.77$, a 77% higher reproduction number. The same paper rejected a shorter-generation-time explanation because, when both variants have the same $R_t < 1$, the variant with the shorter generation interval declines faster, which would have lowered the new variant's frequency during lockdown.

## Sources

- N. G. Davies, S. Abbott, R. C. Barnard, et al., "Estimated transmissibility and impact of SARS-CoV-2 lineage B.1.1.7 in England", Science 372 (2021) eabg3055, "Measuring the new variant's growth rate" and Materials and methods, "Competitive advantage and increased growth rate", <https://doi.org/10.1126/science.abg3055> (PMC8128288).
- J. Wallinga, M. Lipsitch, "How generation intervals shape the relationship between growth rates and reproductive numbers", Proceedings of the Royal Society B 274 (2007) 599–604, <https://doi.org/10.1098/rspb.2006.3754>.
