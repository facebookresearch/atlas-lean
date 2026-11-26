# Counting support networks by zig-zag trail decomposition

**Setting.** Let $N$ be a rooted binary phylogenetic network. A *zig-zag trail* is a connected subgraph whose edges can be ordered $e_1,\dots,e_m$ so that consecutive edges share a head or share a tail. Every maximal zig-zag trail is of one of four types: a *crown* (even $m\ge 4$, closed cyclically as $v_0<v_1>v_2<\cdots<v_{m-1}>v_0$), or a *fence* (any other maximal trail), subdivided into N-fences (odd $m$), M-fences and W-fences (even $m$, with both terminal edges sharing tails, resp. heads). The maximal zig-zag trails partition $E(N)$ uniquely and can be found in $\Theta(|E(N)|)$ time. A spanning subgraph $G$ of $N$ is a *support network* if suppressing its vertices of in- and out-degree $1$ yields a rooted binary phylogenetic network on the same leaf set; support trees are the special case of trees.

**Theorem.** Let $\mathcal{Z}=\{Z_1,\dots,Z_d\}$ be the maximal zig-zag trail decomposition of $N$, and let $\mathcal{A}_N$, $\mathcal{B}_N$, $\mathcal{C}_N$ be the sets of all, inclusion-minimal, and minimum-size support networks of $N$. With Fibonacci numbers $F_n$ ($F_1=F_2=1$), Lucas numbers $L_n$ ($L_1=1, L_2=3$), Padovan numbers $P_n$ ($P_1=P_2=P_3=1$, $P_n=P_{n-2}+P_{n-3}$) and Perrin numbers $Q_n$ ($Q_1=0, Q_2=2, Q_3=3$, $Q_n=Q_{n-2}+Q_{n-3}$),
$$|\mathcal{A}_N| = \prod_{Z_i\ \text{fence}} F_{|E(Z_i)|}\prod_{Z_i\ \text{crown}} L_{|E(Z_i)|}, \qquad |\mathcal{B}_N| = \prod_{Z_i\ \text{fence}} P_{|E(Z_i)|}\prod_{Z_i\ \text{crown}} Q_{|E(Z_i)|},$$
$$|\mathcal{C}_N| = 2^{c}\prod_{Z_i\ \text{M- or W-fence}} \frac{|E(Z_i)|}{2},$$
where $c$ is the number of crowns. Hence $|\mathcal{A}_N| = \Theta(\varphi^{|E(N)|})$ with $\varphi$ the golden ratio and $|\mathcal{B}_N| = \Theta(\psi^{|E(N)|})$ with $\psi \approx 1.3247$ the plastic number, and all three counts are computable in $\Theta(|E(N)|)$ time.

## Expansion

The structure theorem for support trees extends to support networks: a spanning subgraph is a support network exactly when its restriction to every maximal zig-zag trail is an admissible edge subset of that trail, so each of the three families is a direct product over $\mathcal{Z}$ and its size is the product of per-trail counts. Encoding a subset of a trail as a $0$-$1$ string, the admissible strings of a fence or crown satisfy local constraints that make their numbers obey the Fibonacci/Lucas recurrences (all support networks) and the Padovan/Perrin recurrences (inclusion-minimal ones); minimum ones keep exactly the forced edges, leaving two choices per crown and $|E(Z_i)|/2$ choices per M- or W-fence.

## Sources

- T. Suzuki, M. Hayamizu, "Which phylogenetic networks are level-k networks with additional arcs? Structure and algorithms", arXiv:2505.11947, Theorems 2–5. <https://doi.org/10.48550/arXiv.2505.11947>
