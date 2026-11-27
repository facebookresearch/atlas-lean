# Universal sentences of groups in conjunctive normal form

A universal sentence of the language of groups in conjunctive normal form is coded as a finite list of clauses $c_1, \dots, c_m$, each clause a finite list of literals $(b, w)$, where $w$ is a group word in the variables $x_0, x_1, \dots$ and $b \in \{\mathrm{true}, \mathrm{false}\}$. The literal $(\mathrm{true}, w)$ stands for $w = 1$ and $(\mathrm{false}, w)$ for $w \ne 1$. Let $N$ be one more than the largest index of a variable occurring in the words of the code, or $N = 0$ if no variable occurs. The code denotes the sentence

$$\forall x_0 \cdots \forall x_{N-1} \ \bigwedge_{j=1}^{m} \ \bigvee_{(b, w) \in c_j} \bigl(w = 1 \text{ if } b = \mathrm{true};\ w \ne 1 \text{ if } b = \mathrm{false}\bigr),$$

with no quantifiers when $N = 0$.

Every universal sentence of the language of groups is effectively equivalent to such a code.
