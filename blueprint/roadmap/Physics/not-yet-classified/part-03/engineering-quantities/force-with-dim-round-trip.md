# Typed force conversion round trip

For ISQ unit scales $u_1, u_2$ (each assigning a positive magnitude to every base unit) and a dimension $d = \prod_b b^{d_b}$, let $s(d) = \prod_b \bigl(u_1(b)/u_2(b)\bigr)^{d_b} > 0$ be the factor converting a coordinate of dimension $d$ from $u_1$ to $u_2$, and $s'(d)$ the factor from $u_2$ back to $u_1$.

Let $F$ be a real quantity tagged with the force dimension $\mathsf{M\,L\,T^{-2}}$, with coordinate $F_0$. The force-dimensioned quantity with coordinate

$$s'(\mathsf{M\,L\,T^{-2}})\,\bigl(s(\mathsf{M\,L\,T^{-2}})\,F_0\bigr)$$

is equal to $F$.
