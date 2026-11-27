# Substitution for term variable zero

Consider the call-by-value lambda calculus with iso-recursive types. Its types are $\mathrm{unit}$, arrows $a \to b$, de Bruijn type variables $X_n$ ($n \in \mathbb{N}$) and recursive types $\mu.\,a$, where $\mu$ binds type index $0$ in $a$. Its terms are $\mathrm{unit}$, de Bruijn variables $x_n$, abstractions $\lambda.\,t$ without a type annotation (binding index $0$ in $t$), applications $t\,u$, and $\mathrm{fold}\,t$ and $\mathrm{unfold}\,t$, neither annotated with a type.

For terms $t, u$ and $j \in \mathbb{N}$, $t[j := u]$ replaces the variable $x_j$ by $u$, keeps $x_n$ for $n < j$, lowers $x_n$ to $x_{n-1}$ for $n > j$, and under each abstraction continues as $t[j+1 := \uparrow^1_0 u]$, where $\uparrow^d_c$ adds $d$ to every term variable of index at least $c$; it commutes with $\mathrm{unit}$, application, $\mathrm{fold}$ and $\mathrm{unfold}$.

The substitution of $u$ into $t$ is the case $j = 0$: it is $t[0 := u]$, which substitutes $u$ for variable $0$ (the variable bound by an enclosing abstraction) and lowers the other free variables by one. When $u$ is a value, $(\lambda.\,t)\,u$ takes one call-by-value step to $t[0 := u]$.

## Sources

- B. C. Pierce, *Types and Programming Languages*, MIT Press, 2002, Chapter 20 (iso-recursive types). In that presentation $\mathrm{fold}$ and $\mathrm{unfold}$ carry the recursive type as an annotation; here they are unannotated.
