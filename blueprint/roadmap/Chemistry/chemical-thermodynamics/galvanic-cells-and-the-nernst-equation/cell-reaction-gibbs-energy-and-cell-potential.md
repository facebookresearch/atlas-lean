# Cell reaction Gibbs energy and the equilibrium cell potential

In a zero-current equilibrium state with identical terminals, the molar Gibbs energy of the cell reaction is $\Delta_rG_{\mathrm{cell}}=-zFE_{\mathrm{cell,eq}}$; without a liquid junction this gives $E_{\mathrm{cell,eq}}=-\Delta_rG/(zF)$, and a junction of potential $E_j$ adds $E_j$.

Consider a galvanic cell with electron number $z>0$ (positive, and non-integer if the reaction equation is rescaled) and cell reaction with stoichiometric numbers $\nu_i$,
as in [the cell reaction and its electron number](cell-reaction-and-its-electron-number.md), where each ion is
indexed by the phase it occupies. Assume:

1. **identical terminals:** the two terminals have the same composition, temperature and pressure, so the
   electron chemical potential in each is $\mu_e(\mathrm T)=\mu_e^{(0)}-F\phi_{\mathrm T}$ with one common $\mu_e^{(0)}$;
2. **zero-current equilibrium:** each electrode reaction is at equilibrium,

    $$\sum_{i\in\mathrm L}\nu_i\mu_i+z\,\mu_e(\mathrm{LE})=0,\qquad \sum_{j\in\mathrm R}\nu_j\mu_j-z\,\mu_e(\mathrm{RE})=0,$$

    and electrons are in transfer equilibrium between each electron conductor and its terminal,
    $\mu_e(\mathrm{LE})=\mu_e(\mathrm{LT})$, $\mu_e(\mathrm{RE})=\mu_e(\mathrm{RT})$.

Then

$$\Delta_rG_{\mathrm{cell}}=-zF\,(\phi_{\mathrm R}-\phi_{\mathrm L})=-zF\,E_{\mathrm{cell,eq}} .$$

Compare the direct reaction with the same $\nu_i$, the same activities of every species (with the same standard states) and the same $T$ and $p$, in one vessel, with
[molar reaction Gibbs energy](../reaction-gibbs-energy-and-equilibrium-constants/molar-reaction-gibbs-energy.md) $\Delta_rG$. If all ions of the cell reaction
are in one electrolyte phase (no liquid junction), then $\Delta_rG_{\mathrm{cell}}=\Delta_rG$ and
$E_{\mathrm{cell,eq}}=-\Delta_rG/(zF)$. If instead the left and right electrode solutions $\alpha,\beta$ meet at a liquid
junction with $E_j=\phi^\beta-\phi^\alpha$, and the electrode reactions balance charge separately,
$\sum_{i\in\mathrm L}\nu_iz_i=z$ and $\sum_{j\in\mathrm R}\nu_jz_j=-z$, then $\Delta_rG_{\mathrm{cell}}=\Delta_rG-zFE_j$ and
$E_{\mathrm{cell,eq}}=-\Delta_rG/(zF)+E_j$.

## Context

Undergraduate electrochemistry: the open-circuit voltage of a battery is the free energy of its cell reaction per transferred charge. Without a junction, $E_{\mathrm{cell,eq}}=0$ exactly when the cell reaction has zero affinity.

## Depends on

- [Cell reaction, electron number and cell potential](cell-reaction-and-its-electron-number.md)
- [Molar reaction Gibbs energy and its standard value](../reaction-gibbs-energy-and-equilibrium-constants/molar-reaction-gibbs-energy.md)

## Proof depends on

- [Chemical potential in terms of relative activity](../reaction-gibbs-energy-and-equilibrium-constants/chemical-potential-in-terms-of-relative-activity.md)

## Expansion

Adding the two electrode equilibria gives $\Delta_rG_{\mathrm{cell}}=-z[\mu_e(\mathrm{LE})-\mu_e(\mathrm{RE})]$ (DeVoe Eqs. 14.3.4–14.3.6); transfer equilibrium replaces electrodes by terminals (14.3.7), and hypothesis 1 cancels $\mu_e^{(0)}$, giving Eq. 14.3.8. For the direct reaction, write $\mu_i(\phi)=\mu_i(0)+z_iF\phi$; with one solution phase the potential terms cancel by overall charge conservation (Eq. 14.3.9), and with two phases the separate charge balances leave $zF\phi^\alpha-zF\phi^\beta=-zFE_j$ (Eqs. 14.3.11–14.3.12).

## Sources

- H. DeVoe, *Thermodynamics and Chemistry*, 2nd edition, Chemistry LibreTexts edition, Section 14.3, Eqs. 14.3.2–14.3.14 (with Eq. 14.2.2 for the electron chemical potential in a terminal). [Section 14.3](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/DeVoes_Thermodynamics_and_Chemistry/14%3A_Galvanic_Cells/14.03%3A_Molar_Reaction_Quantities_of_the_Cell_Reaction)
