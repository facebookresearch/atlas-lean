# Shifting type variables

Consider the call-by-value lambda calculus with iso-recursive types. Its types are $\mathrm{unit}$, arrows $a \to b$, de Bruijn type variables $X_n$ ($n \in \mathbb{N}$) and recursive types $\mu.\,a$, where $\mu$ binds type index $0$ in $a$. Its terms are $\mathrm{unit}$, de Bruijn variables $x_n$, abstractions $\lambda.\,t$ without a type annotation (binding index $0$ in $t$), applications $t\,u$, and $\mathrm{fold}\,t$ and $\mathrm{unfold}\,t$, neither annotated with a type.

For a type $a$ and $d, c \in \mathbb{N}$, the shift $\uparrow^d_c a$ adds $d$ to every type variable of $a$ whose index is at least the cutoff $c$. It is defined by recursion on $a$: $\uparrow^d_c \mathrm{unit} = \mathrm{unit}$; $\uparrow^d_c (a \to b) = \uparrow^d_c a \to \uparrow^d_c b$; $\uparrow^d_c X_n$ is $X_n$ if $n < c$ and $X_{n+d}$ otherwise; and $\uparrow^d_c (\mu.\,a) = \mu.\,(\uparrow^d_{c+1} a)$. Indices are counted from outside $a$, so variables bound inside $a$ are unchanged.

## Sources

- B. C. Pierce, *Types and Programming Languages*, MIT Press, 2002, Chapter 20 (iso-recursive types). In that presentation $\mathrm{fold}$ and $\mathrm{unfold}$ carry the recursive type as an annotation; here they are unannotated.
