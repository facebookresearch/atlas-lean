# Noninterference for the Volpano–Smith–Irvine type system over an arbitrary order of security classes

Let $SC$ be a set of security classes partially ordered by $\le$, finite or not, and let a location typing $\lambda$ give every memory location $l$ a class $\lambda(l)$. In the
Volpano–Smith–Irvine type system for a deterministic imperative language (assignment, sequencing, conditionals and while loops), expressions have
data types $\tau \in SC$, variables have types $\tau\ \mathrm{var}$ and commands types $\tau\ \mathrm{cmd}$; a command of type $\tau\ \mathrm{cmd}$ assigns only to locations of class $\tau$ or higher, and
the guard of a conditional or loop must have a class below the command type of its branches or body. Subtyping extends $\le$, contravariantly on
command types.

**Theorem (type soundness).** Suppose $\lambda \vdash c : \rho$, $\mu \vdash c \Rightarrow \mu'$ and $\nu \vdash c \Rightarrow \nu'$ are terminating evaluations from memories $\mu$ and $\nu$ with
$\mathrm{dom}(\mu) = \mathrm{dom}(\nu) = \mathrm{dom}(\lambda)$, and let $\tau \in SC$. If $\mu(l) = \nu(l)$ for every $l$ with $\lambda(l) \le \tau$, then $\mu'(l) = \nu'(l)$ for every $l$ with $\lambda(l) \le \tau$.

Thus for every observer level $\tau$ well-typed programs are termination-insensitively noninterfering; the two-point order $L \le H$ with $\tau = L$ is the
usual special case.

## Depends on

- [Security levels, policies and low equivalence](security-levels-policies-and-low-equivalence.md)

## Sources

- D. Volpano, C. Irvine and G. Smith, "A sound type system for secure flow analysis", *Journal of Computer Security* 4(2–3):167–187, 1996, copy at <https://people.cs.ksu.edu/~tamtoft/890/10Fall/Vol+Smi+Irv:JCS-1996.pdf>: Section 3.1 (the secure flow types over a partially ordered $SC$), Section 4 (Figures 2–3, Lemmas 4.1–4.2) and Theorem 6.8 (type soundness).
- A. Sabelfeld and A. C. Myers, "Language-based information-flow security", *IEEE Journal on Selected Areas in Communications* 21(1):5–19, 2003, <https://www.cs.cornell.edu/andru/papers/jsac/sm-jsac03.pdf>: Section III (noninterference condition and the security type system).
