# Degree of a singular modulus

Let $\tau \in \mathbb{H}$ be imaginary quadratic, with
primitive quadratic equation $a\tau^2 + b\tau + c = 0$, where $a, b, c \in \mathbb{Z}$ and
$\gcd(a, b, c) = 1$, and let $\Delta = b^2 - 4ac$ be the discriminant of the singular modulus
$j(\tau)$. Then

$$[\mathbb{Q}(j(\tau)) : \mathbb{Q}] = h(\Delta),$$

the class number of discriminant $\Delta$. In particular $j(\tau)$ is algebraic.

Here $j = E_4^3/\Delta$ is `WLight.jFunction`, with $E_4$ the normalized Eisenstein series of
weight $4$ (constant term $1$) and $\Delta = \eta^{24}$ the modular discriminant, so
$j(\tau) = q^{-1} + 744 + 196884\,q + \cdots$ with $q = e^{2\pi i \tau}$. Since $\tau$ is not
real, the equation is genuinely quadratic, $\Delta < 0$ and $\Delta \equiv 0, 1 \pmod 4$. Fowler
defines $h(\Delta)$ as the class number of the imaginary quadratic order of discriminant $\Delta$.
It is stated here as `MetaMathlibExt.gaussClassNumber`, the number of reduced primitive positive
definite binary quadratic forms of discriminant $\Delta$: every class of primitive positive
definite forms contains exactly one reduced form, and these form classes correspond to the proper
ideal classes of the order of discriminant $\Delta$ (D. A. Cox, *Primes of the Form
$x^2 + ny^2$*, 2nd ed., Wiley (2013), Theorems 2.8 and 7.7).

## Informally uses

- [Form classes and proper ideal classes of an imaginary quadratic order](../../quadratic-forms-sums-of-squares/binary-quaternary-forms/form-classes-and-proper-ideal-classes/form-classes-equiv-proper-ideal-classes.md): after replacing $(a, b, c)$ by $(-a, -b, -c)$ if needed so that $a > 0$, $\tau = \frac{-b + \sqrt{\Delta}}{2a}$ with $\sqrt{\Delta} = i\sqrt{|\Delta|}$, and the lattice $\mathbb{Z} + \mathbb{Z}\tau$ is homothetic to the proper ideal $\mathbb{Z}a + \mathbb{Z}\frac{-b + \sqrt{\Delta}}{2}$ of the order $\mathcal{O}$ of discriminant $\Delta$, so $j(\tau)$ is the $j$-invariant of a proper $\mathcal{O}$-ideal, and the class number $h(\mathcal{O})$ is the Gauss class number $h(\Delta)$
- [Irreducibility of the class equation of an imaginary quadratic order](../adeles-class-field-theory/ring-class-fields/class-equation.md), whose irreducibility over $\mathbb{Q}$ gives $[\mathbb{Q}(j(\tau)) : \mathbb{Q}] = h(\mathcal{O})$

## Sources

- Guy Fowler, *Some uniform effective results on André–Oort for sums of powers in $\mathbb{C}^n$*, Math. Proc. Cambridge Philos. Soc. 180 (2026), 607–641, [§2·1, pp. 612–613](https://doi.org/10.1017/S0305004125101825): the discriminant of a singular modulus is defined on p. 612, and the degree formula is stated on p. 613.
- David A. Cox, *Primes of the form* $x^2 + ny^2$*: Fermat, class field theory, and complex multiplication*, 3rd ed., AMS Chelsea Publishing, Providence, RI, 2022, Theorem 11.1 and Proposition 13.2, as cited by Fowler (§2·1, p. 613) for the integrality and irreducibility of the class equation behind the degree formula.
