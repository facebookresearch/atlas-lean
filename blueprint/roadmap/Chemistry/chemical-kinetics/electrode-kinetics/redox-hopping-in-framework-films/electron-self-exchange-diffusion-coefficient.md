# Electron self-exchange diffusion coefficient

In the Fickian model of redox hopping, the electron diffusion coefficient is $D_e = (k_e/6)\,C^0d^2$.

In a redox-conductive framework film modelled as a three-dimensional array of redox-active sites with total
concentration $C^0 > 0$ and average electron hopping distance $d > 0$, exchanging electrons with second-order
self-exchange rate constant $k_e > 0$, the electron diffusion coefficient is

$$
D_e = \frac{k_e}{6}\,C^0\,d^2 .
$$

The model assumes that the applied potential drops within the double layer, that counterions infiltrate so that no
field acts in the bulk film, and that interactions among redox sites and counterions are negligible, so that charge
moves only down the concentration gradient of the charged species. Measured apparent coefficients
$D_e^{app}$ can be smaller because counterion motion is impeded by the pores.

## Context

Research level. This model frames redox hopping in redox-conductive MOFs, where maximal redox conductivity is expected at a 50:50 mixed-valent composition, at the formal potential of the linker.

## Depends on

None.

## Proof depends on

None.

## Expansion

The factor $1/6$ is that of an isotropic random walk in three dimensions with step $d$ and hop rate $k_eC^0$; the
relation is a stipulated model, not derived from a microscopic transport theory here.

## Sources

- J. Li and S. Ott, "The Molecular Nature of Redox-Conductive Metal–Organic Frameworks", *Accounts of Chemical Research* 57, 2836 (2024), [doi.org](https://doi.org/10.1021/acs.accounts.4c00430), PMC11447836, section "Transient Charge Transport Models and Their Limitations" (the displayed relation for $D_e$).
