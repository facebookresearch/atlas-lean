# Certified quadrature for scale and Green integrals

This page covers a research target: rigorous error bounds for the numerical evaluation of the integrals that give fixation probabilities and occupation times, the scale function and the [Dirichlet Green's function](../selection-duality-and-general-one-dimensional-di/green-function.md), whose integrands are singular at the endpoints and which suffer cancellation near neutrality. Exact formulas, such as [Kimura's fixation probability](../wright-fisher-diffusion/kimura-fixation.md), serve as mathematical oracles, with the floating-point arithmetic controlled separately.

## Expansion

Fix the quadrature rules and the parameter ranges, then state and prove the error bounds, each as a page of its own.

Prerequisites:

- [Dirichlet Green's function of a one-dimensional diffusion](../selection-duality-and-general-one-dimensional-di/green-function.md)
- [Kimura's fixation probability](../wright-fisher-diffusion/kimura-fixation.md)

## Sources

- M. Kimura, Diffusion models in population genetics, *J. Appl. Probab.* 1 (1964), 177–232, <https://doi.org/10.2307/3211856>.
- T. Maruyama, *Stochastic Problems in Population Genetics*, Lecture Notes in Biomathematics 17, Springer (1977), <https://doi.org/10.1007/978-3-642-93065-2>.
