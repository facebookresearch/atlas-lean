# State matrix of a zone thermal network

For zone capacitances $C_i$, inter-zone conductances $G_{ij}$ and ambient conductances $g_{0,i}$ over a finite set of zones, the state matrix acting on zone temperatures has entries

$$A_{ij} = \frac{G_{ij} - \delta_{ij}\bigl(\sum_k G_{ik} + g_{0,i}\bigr)}{C_i},$$

row $i$ being zone equation $i$ without its input terms, divided by $C_i$. The diagonal conductance $G_{ii}$ cancels. The matrix is meaningful for $C_i > 0$; with division by zero taken as $0$, row $i$ is zero when $C_i = 0$.
