# Conservative shared-face finite-volume step

Let $n \in \mathbb{N}$ and index cells by $i \in \mathbb{Z}/n\mathbb{Z}$. For $n > 0$ these are $n$ periodic cells with wraparound, $i + 1$ taken modulo $n$; for $n = 0$ the index type $\mathbb{Z}/0\mathbb{Z}$ is the integers, so the cells form the infinite integer lattice and $i + 1$ is the next integer. With cell length $\Delta x$, cross-section $A$ and time step $\Delta t$ (all real), face fluxes $F : \mathbb{Z}/n\mathbb{Z} \to \mathbb{R}$ (face $i$ is the left face of cell $i$) and cell values $c, c' : \mathbb{Z}/n\mathbb{Z} \to \mathbb{R}$, the update $c \mapsto c'$ is a conservative step when for every cell $i$

$$A\, \Delta x\, c'_i = A\, \Delta x\, c_i + \Delta t\,\bigl(F_i - F_{i+1}\bigr):$$

the mass of cell $i$ gains the inflow $\Delta t\, F_i$ through its left face and loses the outflow $\Delta t\, F_{i+1}$ through its right face.
