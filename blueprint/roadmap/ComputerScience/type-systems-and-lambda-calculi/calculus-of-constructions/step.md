# One-step beta reduction

One-step beta reduction is the smallest relation on terms that
contains every beta step $(\lambda (x : A).\, b)\, a \to b[a/x]$, where $b[a/x]$ substitutes $a$
for the bound variable $x$ in $b$, and that is closed under every term former: a step inside the
function or the argument of an application, inside the type annotation or the body of a
$\lambda$, or inside the domain or the codomain of a $\Pi$ is a step of the whole term.
