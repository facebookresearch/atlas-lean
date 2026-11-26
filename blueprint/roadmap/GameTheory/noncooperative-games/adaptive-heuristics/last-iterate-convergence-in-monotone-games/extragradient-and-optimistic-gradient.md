# Extragradient and optimistic gradient descent-ascent

For an operator $F$ on a closed convex set $\mathcal{Z}$ with Euclidean projection $\Pi_{\mathcal{Z}}$ and step size $\eta > 0$, the extragradient method iterates

$$
z_{t + 1/2} = \Pi_{\mathcal{Z}}\bigl(z_t - \eta F(z_t)\bigr), \qquad z_{t+1} = \Pi_{\mathcal{Z}}\bigl(z_t - \eta F(z_{t+1/2})\bigr),
$$

and optimistic gradient descent-ascent (Popov's method) iterates $w_{t+1} = \Pi_{\mathcal{Z}}(w_t - \eta F(z_t))$, $z_{t+1} = \Pi_{\mathcal{Z}}(w_{t+1} - \eta F(z_t))$, using only one new operator evaluation per step. In a game, each player updates her own block of $z$ with her own gradient, so both methods are uncoupled learning dynamics.

## Depends on

- [Smooth monotone game and monotone variational inequality](smooth-monotone-game-variational-inequality.md)

## Sources

- G. M. Korpelevich, "The extragradient method for finding saddle points and other problems", Ekonomika i Matematicheskie Metody 12 (1976).
- L. D. Popov, "A modification of the Arrow-Hurwicz method for search of saddle points", Mathematical Notes of the Academy of Sciences of the USSR 28(5) (1980).
