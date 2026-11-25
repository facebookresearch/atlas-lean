# Babuška–Brezzi theorem for saddle-point problems

Let $V$ and $Q$ be real Hilbert spaces, let $a$ be a bounded bilinear form on $V \times V$ and $b$ a bounded bilinear form on $V \times Q$, and let $\ker B = \{v \in V : b(v, q) = 0 \text{ for all } q \in Q\}$. For $f \in V'$ and $g \in Q'$, consider the *saddle-point problem*: find $(u, p) \in V \times Q$ with

$$
a(u, w) + b(w, p) = f(w) \quad \forall w \in V, \qquad b(u, q) = g(q) \quad \forall q \in Q.
$$

**Theorem (Babuška–Brezzi).** The problem is well posed for all $f$ and $g$ if and only if both of the following hold.
1. $a$ satisfies the inf-sup conditions on the kernel: there is $\alpha > 0$ such that

    $$
    \sup_{w \in \ker B \setminus \{0\}} \frac{a(v, w)}{\|w\|} \ge \alpha\,\|v\| \quad \text{for every } v \in \ker B \setminus \{0\},
    $$

    and if $w \in \ker B$ has $a(v, w) = 0$ for all $v \in \ker B$, then $w = 0$.
2. $b$ satisfies the inf-sup condition: there is $\beta > 0$ such that

    $$
    \sup_{v \in V \setminus \{0\}} \frac{b(v, q)}{\|v\|} \ge \beta\,\|q\| \quad \text{for every } q \in Q \setminus \{0\}.
    $$

In that case, for any such constants $\alpha$ and $\beta$,

$$
\|u\| \le \frac{1}{\alpha}\|f\| + \frac{1}{\beta}\Bigl(1 + \frac{\|a\|}{\alpha}\Bigr)\|g\|, \qquad
\|p\| \le \frac{1}{\beta}\Bigl(1 + \frac{\|a\|}{\alpha}\Bigr)\|f\| + \frac{\|a\|}{\beta^2}\Bigl(1 + \frac{\|a\|}{\alpha}\Bigr)\|g\|.
$$

**Proof sketch.** The problem is well posed if and only if the restriction of $a$ to $\ker B$ induces an isomorphism $\ker B \to (\ker B)'$, and the operator $B : V \to Q'$ induced by $b$ is surjective. For surjectivity, use that $B$ has closed range with $\operatorname{im}(B^*) = (\ker B)^\perp$. By the [Banach–Nečas–Babuška theorem](continuous-linear-equiv-of-bilinear-form.md), the first property is condition 1, and the second is condition 2. For the estimates, lift $g$ to some $u_g$ with $\|u_g\| \le \|g\|/\beta$, solve on $\ker B$, and then recover $p$ from the inf-sup condition for $b$.

The constants depend only on $\alpha$, $\beta$ and $\|a\|$. So a family of problems is stable uniformly in its parameters when $\alpha$ and $\beta$ stay uniformly bounded away from zero and $\|a\|$ stays uniformly bounded above. That is the mechanism behind locking-free mixed methods for nearly incompressible elasticity, where a Galerkin pair must satisfy a discrete inf-sup condition uniformly in the mesh size and in the Lamé parameter.

## Depends on

- [Banach–Nečas–Babuška theorem](continuous-linear-equiv-of-bilinear-form.md)

## Background

- [Céa's lemma](../c-a-s-lemma/README.md)
- [Strang's lemma](../strang-s-lemma/README.md)

## Sources

- J.-L. Guermond, course notes for Math 661 (Fall 2015), Part VII, Chapter 30 "Well-posedness and saddle point problems", Texas A&M University, <https://people.tamu.edu/~guermond/M661_FALL_2015/chap30.pdf>:
    - Section 30.2.1: Theorem 30.1, well-posedness if and only if the kernel restriction of $A$ is an isomorphism and $B$ is surjective, with proof;
    - Section 30.2.2: Theorem 30.2 (Babuška–Brezzi), conditions (30.5)–(30.6) and the a priori estimates (30.7) with constants $c_1, \dots, c_4$, stated there for reflexive Banach spaces; this page states the Hilbert-space case;
    - Example 30.9: the Stokes equations.
- D. Boffi, *Mixed finite element methods: a crash course*, Lecture 4 "Stokes, stable pairs, and the solution of saddle-point systems", CIMPA school, 2026, <https://www-dimat.unipv.it/boffi/cimpa2026/lecture4.pdf>: the uniform discrete inf-sup condition for conforming Stokes pairs, the Fortin-operator criterion, and the uniformly stable $P_2$–$P_0$ pair.
