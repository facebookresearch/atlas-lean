# Head normal forms and solvable terms

Every untyped λ-term $\tau$ can be written in exactly one way as $\lambda x_1 \dots \lambda x_m.\, v\, t_1 \cdots t_n$ with $m, n \ge 0$, where $v$ is either a variable or a
β-redex $(\lambda x.\, u)\, t$.

- **Head normal form.** $\tau$ is a *head normal form* if $v$ is a variable, that is, $\tau = \lambda x_1 \dots \lambda x_m.\, x\, t_1 \cdots t_n$ for a variable $x$.
  Otherwise the redex $v$ is the *head redex* of $\tau$; it is the leftmost redex of $\tau$. A term is β-normal exactly when it is a head normal
  form $\lambda \vec x.\, x\, t_1 \cdots t_n$ whose arguments $t_1, \dots, t_n$ are β-normal.
- **Head reduction.** The *head reduction* of $\tau$ is the finite or infinite sequence $\tau_0 = \tau, \tau_1, \dots$ in which $\tau_{k+1}$ is obtained by
  contracting the head redex of $\tau_k$; it stops at the first head normal form.
- **Solvable terms.** $\tau$ is *solvable* if for every term $u$ there are variables $x_1, \dots, x_k$ and terms $u_1, \dots, u_k, v_1, \dots, v_l$ ($k, l \ge 0$) with
  $\tau[u_1/x_1, \dots, u_k/x_k]\, v_1 \cdots v_l \simeq_\beta u$. Equivalently, the same holds for $u = I = \lambda x.\, x$. A closed term $\tau$ is solvable exactly when $\tau\, v_1 \cdots v_l \simeq_\beta I$ for some terms $v_1, \dots, v_l$, and
  a term is solvable exactly when its closure $\lambda x_1 \dots \lambda x_n.\, \tau$ over its free variables is. For example, $\Omega = (\lambda x.\, x\,x)(\lambda x.\, x\,x)$ is not
  solvable.

## Depends on

- [Beta equivalence in the untyped term model](../../system-f/the-existing-untyped-beta-conversion-term-model/beta-eq.md)
- [Named, de Bruijn and locally nameless lambda terms](../../syntax-with-binders/named-de-bruijn-and-locally-nameless-lambda-terms.md)

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 2, Section 1 (Proposition 2.2, the definitions of head normal form, head redex, head reduction and solvable term, and the remarks that follow).
