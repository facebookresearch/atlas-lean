# Substitution for a term variable at a given index

Consider the call-by-value lambda calculus with iso-recursive types. Its types are $\mathrm{unit}$, arrows $a \to b$, de Bruijn type variables $X_n$ ($n \in \mathbb{N}$) and recursive types $\mu.\,a$, where $\mu$ binds type index $0$ in $a$. Its terms are $\mathrm{unit}$, de Bruijn variables $x_n$, abstractions $\lambda.\,t$ without a type annotation (binding index $0$ in $t$), applications $t\,u$, and $\mathrm{fold}\,t$ and $\mathrm{unfold}\,t$, neither annotated with a type.

For terms $t, u$ and $j \in \mathbb{N}$, the substitution $t[j := u]$ is defined by recursion on $t$: $\mathrm{unit}[j := u] = \mathrm{unit}$; $x_n[j := u]$ is $x_n$ if $n < j$, $u$ if $n = j$, and $x_{n-1}$ if $n > j$; $(\lambda.\,t)[j := u] = \lambda.\,\bigl(t[j+1 := \uparrow^1_0 u]\bigr)$, where $\uparrow^d_c$ adds $d$ to every term variable of index at least $c$; and it commutes with application, $\mathrm{fold}$ and $\mathrm{unfold}$.

Thus $t[j := u]$ replaces the free variable $j$ by $u$, read in the resulting context, and lowers the free variables above $j$ by one; crossing an abstraction raises both the target index and the free variables of $u$, so they are not captured.

## Sources

- B. C. Pierce, *Types and Programming Languages*, MIT Press, 2002, Chapter 20 (iso-recursive types). In that presentation $\mathrm{fold}$ and $\mathrm{unfold}$ carry the recursive type as an annotation; here they are unannotated.
