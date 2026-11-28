# Zimm–Bragg model of the helix–coil transition

The Zimm–Bragg model treats a chain of $n$ segments, each helical or coil, weighting a configuration by $s^{n_H}\sigma^{\nu_H}$ for $n_H$ helical segments in $\nu_H$ helical stretches; its partition function is $q(n)=(1\;0)\,M^n\,(1\;1)^{\mathsf T}$ with the transfer matrix $M=\begin{pmatrix}1&\sigma s\\1&s\end{pmatrix}$.

**Definition.** A configuration of a chain of $n\ge1$ segments is a word in $\{C,H\}^n$ (coil or helix). For a configuration let $n_H$ be its number of $H$ segments and $\nu_H$ its number of maximal runs of consecutive $H$ (helical stretches). At temperature $T>0$ the propagation weight $s>0$ and the nucleation weight $\sigma>0$ are

$$s=e^{-\Delta g_{HC}/k_BT}=e^{-\Delta G_{HC}/RT},\qquad \sigma=e^{-\Delta g_{\mathrm{nuc}}/k_BT}=e^{-\Delta G_{\mathrm{nuc}}/RT},$$

with molecular free energies $\Delta g$ (per segment for propagation, per stretch for nucleation) paired with $k_B$, or the corresponding molar free energies $\Delta G$ paired with $R$. The statistical weight of a configuration is $s^{n_H}\sigma^{\nu_H}$ (the all-coil chain has weight $1$), the conformational partition function is the sum of the weights of all $2^n$ configurations, and the fractional helicity is

$$q(n)=\sum_{\text{configurations}}s^{n_H}\sigma^{\nu_H},\qquad \theta_H=\frac{\langle n_H\rangle}{n}=\frac{s}{n}\,\frac{\partial\ln q}{\partial s}\Big|_{\sigma\ \text{fixed}}.$$

**Transfer-matrix form.** With states ordered $(C,H)$ and $M_{ab}$ the weight of appending a segment in state $b$ after one in state $a$ (the chain is preceded by a virtual coil segment),

$$M=\begin{pmatrix}1&\sigma s\\1&s\end{pmatrix},\qquad q(n)=\begin{pmatrix}1&0\end{pmatrix}M^{n}\begin{pmatrix}1\\1\end{pmatrix}.$$

For $\sigma=1$ the segments are independent, $q(n)=(1+s)^n$ and $\theta_H=s/(1+s)$. The physically cooperative regime is $0<\sigma<1$ (a nucleation penalty, typically $\sigma\ll1$) with $s$ near $1$; $\sigma>1$ is algebraically allowed but does not describe nucleation-limited helix formation.

## Context

Graduate biophysics. The model explains why helix formation in polypeptides and the melting of long DNA sharpen with chain length: nucleating a helical stretch is costly ($\sigma\ll1$) while extending it is cheap. Seelig and Seelig apply a Zimm–Bragg-type cooperative multistate model to protein unfolding.

## Depends on

- [Partition function of a finite system](../../../../Chemistry/chemical-thermodynamics/canonical-ensemble-of-a-finite-system/partition-function.md)

## Proof depends on

- [Mean occupancy as a logarithmic derivative of the binding polynomial](../cooperativity-and-allostery/mean-occupancy-as-logarithmic-derivative.md)

## Expansion

The helicity formula is the logarithmic-derivative identity applied to $q$ as a polynomial in $s$ with coefficients depending on the fixed $\sigma$. The transfer-matrix identity is proved by induction on $n$: the row vector $(1\;0)M^{k}$ has entries equal to the total weight of length-$k$ configurations ending in $C$ and in $H$, because appending $H$ after $C$ (or after the virtual initial coil) opens a new stretch (factor $\sigma s$), appending $H$ after $H$ extends one (factor $s$), and appending $C$ costs $1$; each stretch thus receives exactly one factor $\sigma$. The independent case follows from the binomial theorem. Both identities were also checked by brute-force enumeration for small $n$.

Remaining decomposition before the page can be marked ready: (i) the induction for the transfer-matrix identity written as a lemma; (ii) the counting of maximal runs ($\nu_H$) defined combinatorially, without the source's truncation formula for the maximal number of stretches, which is not needed.

## Sources

- A. Tokmakoff, *Concepts in Biophysical Chemistry*, LibreTexts, Section 18.1 "Helix–Coil Transition" (read at [chem.libretexts.org](https://chem.libretexts.org/Bookshelves/Biological_Chemistry/Concepts_in_Biophysical_Chemistry_%28Tokmakoff%29/05:_Cooperativity/18:_Cooperativity/18.01:_HelixCoil_Transition)), subsections "Non-cooperative Model" ($q=(1+s)^n$, $\theta_H=s/(1+s)$), "Cooperative Zimm–Bragg Model" (weights $s^{n_H}\sigma^{\nu_H}$ with $k_BT$ in the exponents) and "Multiple stretches" (transfer matrix $\mathbf M$).
- J. Seelig and A. Seelig, "Protein unfolding—thermodynamic perspectives and unfolding models", *International Journal of Molecular Sciences* 24(6) (2023), 5457, [www.mdpi.com](https://www.mdpi.com/1422-0067/24/6/5457); open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC10049513/) (abstract and keywords: Zimm–Bragg theory applied to protein unfolding; context only).
