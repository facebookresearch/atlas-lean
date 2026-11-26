# A source variable lies in the paired locally nameless context

The paired context of $\mathit{names}$ and $\Gamma$ is the list of pairs $(x_i, A_i^{\mathrm{LN}})$ obtained by zipping $\mathit{names} = [x_0, x_1, \dots]$ with $\Gamma = [A_0, A_1, \dots]$ in order, stopping at the shorter list, where $A^{\mathrm{LN}}$ is the translation of simple types into the locally nameless simple types (base $b \mapsto$ base $b$, $A \Rightarrow C \mapsto A^{\mathrm{LN}} \rightsquigarrow  C^{\mathrm{LN}}$).

Let $x$ be a variable of type $A$ in $\Gamma$ with de Bruijn index $i$, and suppose $\mathit{names}$ and $\Gamma$ have the same length. Then the pair $(y, A^{\mathrm{LN}})$, where $y$ is the entry of $\mathit{names}$ at position $i$ (counting from $0$; default $0$ out of range), belongs to the paired context.
