# The release operator of LTL

For LTL formulas $\varphi$ and $\psi$, the release
formula $\varphi \mathbin{\mathbf{R}} \psi$ is defined as
$\neg(\neg\varphi \mathbin{\mathbf{U}} \neg\psi)$, the dual of until.

On an ω-word, $\varphi \mathbin{\mathbf{R}} \psi$ holds at a position when, from that position on,
$\psi$ holds up to and including the first position where $\varphi$ holds, or forever if there is
no such position.
