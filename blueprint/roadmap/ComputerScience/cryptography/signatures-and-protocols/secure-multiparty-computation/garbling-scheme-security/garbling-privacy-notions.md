# Side-information functions and privacy notions for garbling schemes

Let $\mathcal{G} = (\mathrm{Gb}, \mathrm{En}, \mathrm{De}, \mathrm{Ev}, \mathrm{ev})$ be a garbling scheme with security parameter $k$, where $\mathrm{Gb}(1^k, f) = (F, e, d)$. A *side-information function* $\Phi$ maps a function description $f$ to the information $\Phi(f)$ that a garbling is allowed to reveal, such as its size $\Phi_{\mathrm{size}}$, its topology $\Phi_{\mathrm{topo}}$, its topology together with which gates are XOR ($\Phi_{\mathrm{xor}}$), or the whole circuit $\Phi_{\mathrm{circ}}$. The notions are defined by single-query games against a two-stage adversary:
- *prv.ind*: the adversary submits $(f_0, x_0), (f_1, x_1)$ with $\Phi(f_0) = \Phi(f_1)$ and $\mathrm{ev}(f_0, x_0) = \mathrm{ev}(f_1, x_1)$, receives $(F, \mathrm{En}(e, x_b), d)$ for a hidden bit $b$ and guesses $b$; its advantage is $|2\Pr[\text{correct}] - 1|$.
- *prv.sim*: there is a simulator $\mathcal{S}$ such that, for the adversary's chosen $(f, x)$, the tuple $(F, \mathrm{En}(e, x), d)$ is indistinguishable from $\mathcal{S}(1^k, \mathrm{ev}(f, x), \Phi(f))$.
- *obv.ind*: the adversary submits $(f_0, x_0), (f_1, x_1)$ with $\Phi(f_0) = \Phi(f_1)$, with no condition on the outputs $\mathrm{ev}(f_0, x_0), \mathrm{ev}(f_1, x_1)$, receives $(F, \mathrm{En}(e, x_b))$ without $d$ for a hidden bit $b$ and guesses $b$; its advantage is $|2\Pr[\text{correct}] - 1|$.
- *obv.sim*: there is a simulator $\mathcal{S}$ such that, for the adversary's chosen $(f, x)$, the pair $(F, \mathrm{En}(e, x))$ (without $d$) is indistinguishable from $\mathcal{S}(1^k, \Phi(f))$, the simulator not being given the output.
- *aut*: given $(F, \mathrm{En}(e, x))$ the adversary must produce a garbled output $Y \ne \mathrm{Ev}(F, \mathrm{En}(e,x))$ with $\mathrm{De}(d, Y) \ne \bot$.
In the *adaptive* (prv1) variant the adversary sees $F$ before choosing $x$. A scheme is secure for a notion if every probabilistic polynomial-time adversary has negligible advantage (for prv.sim: for every adversary there is a polynomial-time simulator).

## Depends on

- [Garbling schemes and Yao's construction](../garbled-circuits-and-the-correctness-of-yao-s.md)
- [Negligible advantage](../../../security-games/asymptotic-security/negligible-adv.md)
- [Distinguishing advantage](../../../security-games/games-and-advantages/advantage.md)

## Sources

- Mihir Bellare, Viet Tung Hoang and Phillip Rogaway, "Foundations of Garbled Circuits", Proceedings of the 2012 ACM Conference on Computer and Communications Security, 2012.
