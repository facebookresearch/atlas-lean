# Conditional duality between channel identification and time decoding

Let $\mathcal H$ be the space of trigonometric polynomials of bandwidth $\Omega$ and order $L$ on $[0, T]$, $T = 2\pi L/\Omega$,

$$u(t) = \sum_{l=-L}^{L} u_l\, e_l(t), \qquad e_l(t) = \frac{1}{\sqrt T}\exp\!\Big(\frac{j l \Omega t}{L}\Big),$$

with inner product $\langle u, w\rangle = \int_0^T u(t)\overline{w(t)}\,dt$. It is a reproducing kernel Hilbert space with the Dirichlet kernel $K(s,t) = \sum_{l=-L}^{L} e_l(s)\overline{e_l(t)}$. A linear filter has impulse response $h \in L^1(\mathbb{R})$ supported in $[0, T]$, and its projection onto the input space is

$$(\mathcal P h)(t) = \int_0^T h(s)\,\overline{K(s,t)}\,ds .$$

In a [Filter]-[Ideal IAF] circuit, the filter output $v = u * h$ drives an ideal integrate-and-fire neuron with bias $b > 0$, capacitance $C > 0$ and threshold $\delta > 0$, producing spike times $t_1 < \dots < t_n$ in $[0, T]$ with the t-transform

$$\int_{t_k}^{t_{k+1}} (u * h)(s)\,ds = q_k, \qquad q_k = C\delta - b\,(t_{k+1} - t_k), \quad k = 1, \dots, n-1 .$$

Conditional duality: for every input $u \in \mathcal H$ the circuit with filter $h$ is input/output equivalent to the circuit with filter $\mathcal P h$, since $u * h = u * \mathcal P h$ on $[0, T]$. Hence identifying $\mathcal P h$ from a known input $u$ and the observed spikes is the same problem as decoding the signal $\mathcal P h$ encoded by a [Filter]-[Ideal IAF] time encoding machine whose filter is $u$. Moreover each measurement is an inner product with the filter projection: $q_k = \langle \mathcal P h, \phi_k\rangle$ for $\phi_k = \sum_l \phi_{l,k} e_l \in \mathcal H$ with $\phi_{l,k} = \sqrt T \int_{t_k}^{t_{k+1}} \overline{u_l}\, \overline{e_l(t)}\,dt$.

## Expansion

By the reproducing property, $u(t-w) = \int_0^T u(z)\overline{K(z, t-w)}\,dz$; exchanging integrals and using $K(z, t-w) = K(w, t-z)$ turns $\int h(w) u(t-w)\,dw$ into the periodic convolution $(u * \mathcal P h)(t)$. Commuting the convolution swaps the roles of input and filter, which is the duality. The measurement functional $w \mapsto \int_{t_k}^{t_{k+1}} (u * w)$ is bounded on $\mathcal H$, so the Riesz representation theorem gives $\phi_k$, and evaluating it on the basis $e_l$ gives the coefficients. The point is that a neuron which spikes in response to a known stimulus is sampling its own upstream filter, so time-decoding machinery transfers to system identification of dendritic or receptor processing. The equivalence is conditional because it holds only for inputs in $\mathcal H$. This is Proposition 7 and Lemma 8 of the source.

## Sources

- A. A. Lazar, Y. B. Slutskiy, Channel identification machines, Comput. Intell. Neurosci. 2012 (2012), 209590, Definitions 1, 5, 6, Proposition 7, Lemma 8, Eqs. (1)–(8). <https://doi.org/10.1155/2012/209590> (PMCID: PMC3505648)
