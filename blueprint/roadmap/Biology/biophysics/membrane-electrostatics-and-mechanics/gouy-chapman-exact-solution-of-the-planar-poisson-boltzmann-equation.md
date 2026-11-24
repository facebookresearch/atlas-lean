# Gouy–Chapman solution of the planar Poisson–Boltzmann equation

For a planar charged surface in a symmetric 1:1 electrolyte with Debye length $\lambda_D > 0$ and Bjerrum length $l_B > 0$, write the potential in thermal units, $\Phi = e\phi/k_B T$, and distance from the surface in Debye lengths, $x$. The Poisson–Boltzmann equation becomes $\Phi'' = \sinh\Phi$ on $x > 0$ (Tokmakoff, Sec. 6.7). Its solutions with $\Phi(x) \to 0$ and $\Phi'(x) \to 0$ as $x \to \infty$ and surface value $\Phi(0) = \Phi_0$ are
$$\Phi(x) = 2\ln\frac{1 + g e^{-x}}{1 - g e^{-x}}, \qquad g = \tanh(\Phi_0/4) \in (-1, 1),$$
equivalently $\tanh(\Phi(x)/4) = g e^{-x}$. If the surface carries number charge density $\sigma > 0$ (charge density $e\sigma$), the boundary condition $\Phi'(0) = -2\lambda_D/b$ with the Gouy–Chapman length $b = 1/(2\pi l_B \sigma)$ gives $g = -b/\lambda_D + \sqrt{1 + (b/\lambda_D)^2}$, which is the source's formula with $x_0 = e/(2\pi l_B \sigma_{\text{charge}}) = b$. For $\sigma < 0$ the solution is the negative of the one for $|\sigma|$, and for $\sigma = 0$ it is $\Phi \equiv 0$ ($g = 0$); neither case is given by the formula in $b$.

## Expansion

1. The model: the one-dimensional Poisson–Boltzmann equation for a 1:1 electrolyte in reduced units, the boundary conditions at the surface (fixed potential or fixed charge) and at infinity, and the parameters $\lambda_D, l_B > 0$.
2. The first integral $\Phi'^2 = 4\sinh^2(\Phi/2)$ for decaying solutions and the sign $\Phi' = -2\sinh(\Phi/2)$, valid for both signs of $\Phi_0$ (derived, not quoted).
3. Integration to $\tanh(\Phi/4) = g e^{-x}$ and uniqueness of the decaying solution for given $\Phi_0$ (derived).
4. The charge boundary condition and the relation $\sinh(\Phi_0/2) = \lambda_D/b$, solved for $g$ when $\sigma > 0$; the cases $\sigma < 0$ and $\sigma = 0$ (derived).

## Sources

- A. Tokmakoff, *Concepts in Biophysical Chemistry*, LibreTexts, Sec. 6.7 Ion Distributions Near a Charged Interface, Gouy–Chapman model. <https://chem.libretexts.org/Bookshelves/Biological_Chemistry/Concepts_in_Biophysical_Chemistry_(Tokmakoff)/01%3A_Water_and_Aqueous_Solutions/06%3A_Electrical_Properties_of_Water_and_Aqueous_Solutions/6.07%3A_Ion_Distributions_Near_a_Charged_Interface>
- Original model: G. Gouy, Sur la constitution de la charge électrique à la surface d'un électrolyte, J. Phys. Théor. Appl. 9 (1910), 457–468. <https://doi.org/10.1051/jphystap:019100090045700> The solution follows Tokmakoff, Sec. 6.7.
- Original model: D. L. Chapman, A contribution to the theory of electrocapillarity, Philos. Mag. 25 (1913), 475–481. <https://doi.org/10.1080/14786440408634187> The solution follows Tokmakoff, Sec. 6.7.
