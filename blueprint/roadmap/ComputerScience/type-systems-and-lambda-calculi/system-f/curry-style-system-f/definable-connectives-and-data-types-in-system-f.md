# Definable connectives and data types in System F

In [Church-style System F](../the-five-typing-rules-of-pure-system-f/typing.md), with $\alpha$ fresh:

- $\bot = \forall \alpha.\, \alpha$, with $M\, \tau : \tau$ for $M : \bot$;
- $\tau \wedge \sigma = \forall \alpha.\, (\tau \to \sigma \to \alpha) \to \alpha$, with $\langle P, Q \rangle = \Lambda \alpha.\, \lambda z.\, z\, P\, Q$, $\pi_1(M) = M\, \tau\, (\lambda x\, y.\, x)$ and $\pi_2(M) = M\, \sigma\, (\lambda x\, y.\, y)$;
- $\tau \vee \sigma = \forall \alpha.\, (\tau \to \alpha) \to (\sigma \to \alpha) \to \alpha$, with $\mathrm{in}_1(M) = \Lambda \alpha.\, \lambda u\, v.\, u\, M$, $\mathrm{in}_2(M) = \Lambda \alpha.\, \lambda u\, v.\, v\, M$ and
  $\mathrm{case}(L; x.M; y.N) = L\, \rho\, (\lambda x.\, M)\, (\lambda y.\, N)$ for $M, N : \rho$;
- $\exists \alpha.\, \sigma = \forall \beta.\, (\forall \alpha.\, \sigma \to \beta) \to \beta$ with $\beta \notin \mathrm{FV}(\sigma)$, with $\mathrm{pack}\ M, \tau = \Lambda \beta.\, \lambda x.\, x\, \tau\, M$ and
  $\mathrm{abstype}\ \alpha\ \mathrm{with}\ x : \sigma\ \mathrm{is}\ M\ \mathrm{in}\ N = M\, \rho\, (\Lambda \alpha.\, \lambda x.\, N)$ for $N : \rho$, where $\alpha$ is not free in $\rho$ or in the type of any free variable of $N$ other than $x$;
- $\mathrm{Bool} = \forall \alpha.\, \alpha \to \alpha \to \alpha$ and $\omega = \forall \alpha.\, (\alpha \to \alpha) \to \alpha \to \alpha$, with Church numerals $c_n = \Lambda \alpha.\, \lambda f\, x.\, f^n\, x$ and
  $\mathrm{succ} = \lambda n.\, \Lambda \alpha.\, \lambda f\, x.\, f\, (n\, \alpha\, f\, x)$.

These terms satisfy the typing rules and β-rules of the corresponding constructs up to $\twoheadrightarrow_\beta$ (η is not implemented: $\langle \pi_1(y), \pi_2(y) \rangle$ is normal). The
function $n \mapsto n^n$ is defined by $\lambda n{:}\omega.\, \Lambda \alpha.\, \lambda f{:}\alpha \to \alpha.\, \lambda x{:}\alpha.\, n\, (\alpha \to \alpha)\, (n\, \alpha)\, f\, x$ of type $\omega \to \omega$, a use of
polymorphism that simple types do not allow: applied to $c_n$ it β-reduces to $c_{n^n}$, including $c_1$ for $n = 0$. The notes print $\lambda n.\, n\, (\alpha \to \alpha)\, (n\, \alpha)$,
without the type abstraction; with $\Lambda \alpha$ added but without the abstractions over $f$ and $x$, the term applied to $c_0$ reduces to
$\Lambda \alpha.\, \lambda f{:}\alpha \to \alpha.\, f$, which is only η-equal to $c_1$.

## Depends on

- [Extrinsic typing of pure System F terms](../the-five-typing-rules-of-pure-system-f/typing.md)
- [System F in Church style](../../normalization-and-logical-relations/system-f-in-church-style.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Section 12.4, Definitions 12.4.1–12.4.3 and 12.4.5, and the discussion of Bool, $\omega$, Church numerals, successor and $n \mapsto n^n$ before Proposition 12.4.4.
