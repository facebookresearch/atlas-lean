# Förster resonance energy transfer efficiency

In Förster theory the donor-to-acceptor transfer rate falls as the inverse sixth power of their distance, $k_F=k_D(R_0/r)^6$; for a positive Förster radius $R_0$ the transfer efficiency is $E=R_0^6/(R_0^6+r^6)$, equal to $1/2$ at $r=R_0$, and it can also be read from donor lifetimes as $E=1-\tau_{DA}/\tau_D$.

**Setting.** A donor chromophore D and an acceptor A are held at a single fixed distance $r>0$. In the absence of the acceptor the donor's excited state decays with total rate $k_D=1/\tau_D>0$; adding the acceptor opens one additional channel, energy transfer at rate $k_F$, and does not change the donor's intrinsic decay rates. Förster's result gives

$$k_F=k_D\left(\frac{R_0}{r}\right)^{6},\qquad R_0^6=\frac{9000\,(\ln10)\,\kappa^2\,Q_D\,J}{128\,\pi^5\,n^4\,N_A},$$

where $Q_D$ is the donor quantum yield, $n>0$ the refractive index of the medium, $N_A$ Avogadro's constant, $\kappa^2\in[0,4]$ an orientation factor (the range as stated by Visser, Vysotski and Lee), and $J$ the spectral overlap integral. In the standard normalization

$$J=\int f_D(\lambda)\,\varepsilon_A(\lambda)\,\lambda^4\,d\lambda,$$

with $f_D$ the donor emission spectrum normalized to unit area in $\lambda$ and $\varepsilon_A$ the decadic molar absorptivity of the acceptor in M$^{-1}$cm$^{-1}$. With $\lambda$ in cm, $J$ is in M$^{-1}$cm$^3$ and the displayed formula gives $R_0$ in cm; equivalently, with $\lambda$ in nm and $J$ in M$^{-1}$cm$^{-1}$nm$^4$, $R_0=0.02108\,(\kappa^2Q_Dn^{-4}J)^{1/6}$ nm. The value $\kappa^2=2/3$ applies when both transition dipoles reorient isotropically, independently and fast compared with the donor excited-state lifetime in the presence of transfer (and without it, where relevant).

**Statement.** Assume $R_0>0$ (that is, $\kappa^2>0$, $Q_D>0$ and $J>0$). The transfer efficiency, the probability that an absorbed donor photon leads to transfer, is

$$E=\frac{k_F}{k_F+k_D}=\frac{R_0^6}{R_0^6+r^6}=\frac{1}{1+(r/R_0)^6},$$

a strictly decreasing function of $r>0$ with $E(R_0)=1/2$, $E\to1$ as $r\to0^+$ and $E\to0$ as $r\to\infty$. With $\tau_{DA}=1/(k_F+k_D)$ the donor lifetime in the presence of the acceptor,

$$E=1-\frac{\tau_{DA}}{\tau_D}.$$

If $R_0=0$ (for example $\kappa^2=0$ or $J=0$), then $k_F=0$ and $E\equiv0$. The limit $r\to0^+$ is a property of the formula; the dipole–dipole theory itself is not valid at contact distances.

## Context

Undergraduate to graduate biophysics. FRET is a "spectroscopic ruler" for distances of roughly 1 to 10 nm and the basis of many proximity and hybridization assays; $R_0$ values of 4 to 8 nm are typical for single-molecule dye pairs (empirical). A quenching-based proximity readout of the kind described on [Stern–Volmer fluorescence quenching](stern-volmer-quenching.md) can be analysed through the donor channel with this formula only if the Förster model is separately justified for the dye–quencher pair; intensity measurements alone neither establish that assumption nor yield a distance.

## Depends on

None.

## Proof depends on

None.

## Expansion

Proof (given the Förster rate law as a hypothesis): the efficiency is the branching ratio of two competing first-order decay channels, the lifetime form follows because the donor's total decay rate with acceptor is $k_F+k_D$, and monotonicity and limits are immediate from $E=1/(1+(r/R_0)^6)$ with $R_0>0$. The numerical prefactor $0.02108$ was recomputed from the displayed $R_0^6$ formula with $1\,\mathrm{nm}^4=10^{-28}\,\mathrm{cm}^4$.

Remaining decomposition before the page can be marked ready: (i) the Förster rate law and the expression for $R_0$ belong on a separate model page with their physical assumptions (weak dipole–dipole coupling, point dipoles, the orientation average), whose derivation is outside this page; (ii) the definition of $J$: Visser et al. state its normalization and units in text (consistent with the $\lambda^4$ weighting above), but their formula is an image, so a text-readable statement of the integrand is still to be cited; (iii) distance distributions and photon statistics, which make measured efficiency histograms broader than one value of $r$, need their own model page.

## Sources

- B. Schuler, "Single-molecule FRET of protein structure and dynamics – a primer", *Journal of Nanobiotechnology* 11 (Suppl. 1) (2013), S2, [doi.org](https://doi.org/10.1186/1477-3155-11-S1-S2); open-access copies read: [link.springer.com](https://link.springer.com/article/10.1186/1477-3155-11-S1-S2) and [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC4029180/), section "Förster resonance energy transfer (FRET)", Eqs. 1–4 (rate law, $R_0^6$, orientation factor, efficiency) and Fig. 1, and the lifetime relation $E=1-\tau_{DA}/\tau_D$ for a single fixed distance in the section on single-molecule measurements.
- A. J. W. G. Visser, E. S. Vysotski and J. Lee, "Critical transfer distance determination between FRET pairs", Photobiological Sciences Online (read at [photobiology.info](https://photobiology.info/Experiments/Biolum-Expt.html)), section "Recapitulation of Relevant Equations", Eq. 3 (rendered as an image; the text states the overlap convention: donor spectrum normalized to unit integral, acceptor molar absorptivity in M$^{-1}$cm$^{-1}$, wavelength in nm, $J$ in M$^{-1}$cm$^{-1}$nm$^4$), and the description of the Excel procedure, where the orientation factor $\kappa^2$ "can adopt any value between 0 and 4".
