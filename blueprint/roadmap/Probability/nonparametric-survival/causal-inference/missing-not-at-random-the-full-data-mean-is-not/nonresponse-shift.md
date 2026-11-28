# Nonresponse Shift

For $\delta \in \mathbb R$, the $\delta$-shift of nonrespondents is the map $s_\delta : \{0,1\} \times \mathbb R \to \{0,1\} \times \mathbb R$ adding $\delta$ to the outcome of every nonrespondent:

$$s_\delta(r, y) = \begin{cases} (r, y) & r = 1, \\ (r, y + \delta) & r = 0. \end{cases}$$

Pushing a full-data law of $(r, y)$ forward along $s_\delta$ changes only the outcome law of the nonrespondents; this is the $\delta$-adjustment of pattern-mixture sensitivity analysis.
