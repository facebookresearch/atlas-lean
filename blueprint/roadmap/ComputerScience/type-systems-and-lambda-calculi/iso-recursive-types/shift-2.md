# Shifting term variables

Consider the call-by-value lambda calculus with iso-recursive types. Its types are $\mathrm{unit}$, arrows $a \to b$, de Bruijn type variables $X_n$ ($n \in \mathbb{N}$) and recursive types $\mu.\,a$, where $\mu$ binds type index $0$ in $a$. Its terms are $\mathrm{unit}$, de Bruijn variables $x_n$, abstractions $\lambda.\,t$ without a type annotation (binding index $0$ in $t$), applications $t\,u$, and $\mathrm{fold}\,t$ and $\mathrm{unfold}\,t$, neither annotated with a type.

For a term $t$ and $d, c \in \mathbb{N}$, the shift $\uparrow^d_c t$ adds $d$ to every variable of $t$ whose index is at least the cutoff $c$. It is defined by recursion on $t$: $\mathrm{unit}$ is unchanged; $x_n$ becomes $x_n$ if $n < c$ and $x_{n+d}$ otherwise; $\uparrow^d_c (\lambda.\,t) = \lambda.\,(\uparrow^d_{c+1} t)$; and the shift commutes with application, $\mathrm{fold}$ and $\mathrm{unfold}$. Indices are counted from outside $t$, so variables bound inside $t$ are unchanged.

## Sources

- B. C. Pierce, *Types and Programming Languages*, MIT Press, 2002, Chapter 20 (iso-recursive types). In that presentation $\mathrm{fold}$ and $\mathrm{unfold}$ carry the recursive type as an annotation; here they are unannotated.
