# Flat closure conversion

Given accessors $\mathrm{acc}$, a map from natural numbers to
target terms, the flat conversion $C_{\mathrm{acc}}(t)$ of a raw term $t$ is defined by recursion
on $t$. A variable $i$ becomes $\mathrm{acc}(i)$. A lambda $\lambda.\,b$, whose parameter type is
ignored, becomes the pair $(\mathsf{code}\,C_{\mathrm{acc}'}(b), e)$. Here $i_1, \dots, i_n$ are
the captured variables of $b$, the environment $e$ is
$(\mathrm{acc}(i_1), (\mathrm{acc}(i_2), \dots, (\mathrm{acc}(i_n), \mathsf{unit})\dots))$, and
$\mathrm{acc}'$ sends $0$ to $\mathsf{fst}\,(\mathsf{var}\,0)$ and $j + 1$ to
$\mathsf{fst}\,(\mathsf{snd}^{k+1}\,(\mathsf{var}\,0))$, where $k$ is the position of $j$ in that
list, counting from $0$ (the length $n$ if $j$ does not occur). An application $f\,a$ becomes
$\mathsf{let}\ C_{\mathrm{acc}}(f)\ \mathsf{in}\ (\mathsf{fst}\,(\mathsf{var}\,0))\,
(C_{\mathrm{acc}^{+}}(a), \mathsf{snd}\,(\mathsf{var}\,0))$, where $\mathsf{var}\,0$ is the
variable bound by the $\mathsf{let}$ and $\mathrm{acc}^{+}(i)$ is the shift of $\mathrm{acc}(i)$.
