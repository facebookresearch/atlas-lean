# Conservative shared-face finite-volume step

On $n$ periodic cells indexed by $i \in \mathbb{Z}/n\mathbb{Z}$, with cell length $\Delta x$, cross-section $A$ and time step $\Delta t$ (all real), face fluxes $F : \mathbb{Z}/n\mathbb{Z} \to \mathbb{R}$ (face $i$ is the left face of cell $i$) and cell values $c, c' : \mathbb{Z}/n\mathbb{Z} \to \mathbb{R}$, the update $c \mapsto c'$ is a conservative step when for every cell $i$

$$A\, \Delta x\, c'_i = A\, \Delta x\, c_i + \Delta t\,\bigl(F_i - F_{i+1}\bigr),$$

with $i + 1$ taken modulo $n$: the mass of cell $i$ gains the inflow $\Delta t\, F_i$ through its left face and loses the outflow $\Delta t\, F_{i+1}$ through its right face.
