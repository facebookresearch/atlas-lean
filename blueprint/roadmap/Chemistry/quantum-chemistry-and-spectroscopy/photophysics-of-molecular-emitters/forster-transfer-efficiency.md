# Efficiency of Förster resonance energy transfer

Transfer is one more first-order channel of the excited donor, so its efficiency depends on the separation alone through the sixth power of the ratio to the Förster radius, and it is measured as the fractional shortening of the donor lifetime.

Let a donor have intrinsic decay rate constant $k_{\mathrm{D}} = 1/\tau^{0}_{\mathrm{D}} > 0$ and let an acceptor at separation $r > 0$ add only the transfer channel, of rate constant $k_{\mathrm{T}} = k_{\mathrm{D}}(R_{0}/r)^{6}$ with Förster radius $R_{0} > 0$, leaving the donor's other rate constants and its preparation unchanged. The transfer quantum efficiency is

$$
\Phi_{\mathrm{T}} = \frac{k_{\mathrm{T}}}{k_{\mathrm{D}} + k_{\mathrm{T}}} = \frac{1}{1 + (r/R_{0})^{6}} = 1 - \frac{\tau_{\mathrm{D}}}{\tau^{0}_{\mathrm{D}}} ,
$$

where $\tau_{\mathrm{D}}$ is the donor lifetime in the presence of the acceptor.

The middle expression needs $R_{0} > 0$; in the degenerate case $R_{0} = 0$, which the rate model allows when the spectral overlap or the orientation factor vanishes, the transfer rate is zero, $\Phi_{\mathrm{T}} = 0$ and the lifetime is unchanged, while the ratio $(r/R_{0})$ is undefined. For $R_{0}, r > 0$ the efficiency decreases strictly in $r$, equals $1/2$ at $r = R_{0}$ and tends to $0$ as $r \to \infty$; the limit $1$ as $r \to 0$ is an extrapolation of the model past the contact distance where it holds, not an attainable measurement.

The identity with the lifetime ratio is for a single donor–acceptor pair at a fixed separation. In an ensemble with a distribution of separations or orientations, the yield-based and decay-time-based estimates are averages of different functionals of that distribution, multiexponential decays being the usual symptom, so the two agree only under a stated population model and are not interchangeable in general.

## Depends on

- [Förster resonance energy transfer rate](forster-resonance-energy-transfer-rate.md)
- [Lifetime of an excited state](excited-state-lifetime.md)

## Proof depends on

- [Branching of competing first-order decay channels](branching-of-competing-decay-channels.md)

## Expansion

The branching identity for the two channels $k_{\mathrm{D}}$ and $k_{\mathrm{T}}$ gives the first equality; substituting $k_{\mathrm{T}} = k_{\mathrm{D}}(R_{0}/r)^{6}$ and cancelling $k_{\mathrm{D}} > 0$ gives the second, under $R_{0}, r > 0$. For the third, $\tau_{\mathrm{D}} = (k_{\mathrm{D}} + k_{\mathrm{T}})^{-1}$, so $\tau_{\mathrm{D}}/\tau^{0}_{\mathrm{D}} = k_{\mathrm{D}}/(k_{\mathrm{D}} + k_{\mathrm{T}}) = 1 - \Phi_{\mathrm{T}}$. Monotonicity and the endpoint values follow from monotonicity of $x \mapsto 1/(1 + x^{6})$ on the positive reals.

## Context

Graduate. The measurable form of the transfer model: efficiencies are read from donor lifetimes, which is how energy-transfer designs are validated experimentally.

## Sources

- Silvia E. Braslavsky, *Glossary of terms used in photochemistry, 3rd edition (IUPAC Recommendations 2006)*, Pure and Applied Chemistry 79 (2007) 293–465. DOI [10.1351/pac200779030293](https://doi.org/10.1351/pac200779030293), entry “Förster-resonance-energy transfer (FRET)”, p. 343, Note 4, which gives the transfer quantum efficiency and its lifetime form.
