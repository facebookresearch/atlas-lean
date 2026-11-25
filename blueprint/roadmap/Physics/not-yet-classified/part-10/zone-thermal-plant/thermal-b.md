# Zone thermal input matrix

For a finite set of zones with capacities $C_i$ and outdoor conductances $g_{0,i}$, the input matrix for the input $(T_{out}, P)$ is $\operatorname{diag}(1/C)\,[\,g_0 \mid I\,]$, with $1/C_i = 0$ when $C_i = 0$ by the convention $x/0 = 0$: the outside temperature enters zone $i$ with gain $g_{0,i}/C_i$, and the heating power of zone $j$ enters zone $j$ alone with gain $1/C_j$.
