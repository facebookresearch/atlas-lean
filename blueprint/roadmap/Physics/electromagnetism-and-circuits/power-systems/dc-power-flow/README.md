# DC power flow

Lossless DC power flow on a network whose branches `e` run from a tail `t(e)` to a head `h(e)`: with
real susceptances `b_e` and node phase angles `θ_v`, the branch flows are
`f_e = b_e (θ_{t(e)} - θ_{h(e)})` and the nodal injections are `p = L_b θ`, for the
susceptance-weighted Laplacian `L_b`. With unit-magnitude voltages `exp(i θ_v)` and lossless
admittances `-i b_e`, the AC sending-end real power is `b_e sin(θ_{t(e)} - θ_{h(e)})`; when every
susceptance is positive, it differs from `f_e` by at most `b_e |θ_{t(e)} - θ_{h(e)}|³ / 6`.

## The lossless DC model

- [DC branch flow](dc-branch-flow.md)
- [DC nodal injection](dc-injection.md)
- [Susceptance-weighted Laplacian](weighted-laplacian.md)
- [DC flow is susceptance times the angle difference across the branch](dc-branch-flow-apply.md)
- [The DC injection is the weighted Laplacian applied to the angles](dc-injection-eq-weighted-laplacian-mul-v.md)
- [The weighted Laplacian in terms of the head-positive incidence](weighted-laplacian-eq-incidence-matrix.md)
- [The weighted Laplacian annihilates constant angle vectors](weighted-laplacian-mul-vec-const.md)
- [Reversing all branches negates the DC flows](dc-branch-flow-reverse.md)

## Kernel and grounded block of the weighted Laplacian

- [Energy identity for the susceptance-weighted Laplacian](dot-product-weighted-laplacian-mul-vec.md)
- [Kernel of the weighted Laplacian for nonnegative susceptances](weighted-laplacian-mul-vec-eq-zero-iff.md)
- [Kernel of the weighted Laplacian of nonnegative connected networks](weighted-laplacian-mul-vec-eq-zero-iff-o.md)
- [Positive definite grounded Laplacian of nonnegative connected networks](grounded-weighted-laplacian-pos-def.md)
- [Invertible grounded Laplacian of nonnegative connected networks](grounded-weighted-laplacian-is-unit.md)

## Grounded DC load-flow solve

- [Weighted Laplacian with the reference row and column deleted](grounded-laplacian.md)
- [Grounded DC angles from the reduced susceptance matrix](grounded-angles.md)
- [The grounded angles vanish at the reference node](grounded-angles-ref.md)
- [The reduced matrix of a connected network with b > 0 is invertible](grounded-laplacian-is-unit.md)
- [Injections of the form L_b θ are balanced](sum-eq-zero-of-weighted-laplacian-mul-ve.md)
- [For b > 0 on a connected network, grounded angles solve balanced loads](weighted-laplacian-mul-vec-grounded-angl.md)
- [With b > 0 on a connected network, grounded solutions are unique](eq-grounded-angles.md)
- [With b > 0 on a connected network, all solutions carry the same flows](dc-branch-flow-eq-grounded-angles.md)
- [Grounded DC load flow on a connected network with b > 0](l2-correct.md)

## The lossless unit-magnitude AC model

- [Unit-magnitude voltage phasor of a node](unit-voltage.md)
- [Lossless branch admittance](lossless-admittance.md)
- [Branch current from an admittance and a voltage drop](branch-current.md)
- [Sending-end real power of a lossless branch](ac-branch-real-power.md)
- [The branch drop through the electrical incidence is tail minus head](branch-drop-electrical-incidence.md)
- [Nodal current injection as branch currents plus shunt current](node-injection-eq-sum-branch-current.md)
- [Unit-magnitude voltages have modulus one](norm-unit-voltage.md)
- [A zero phase angle gives the unit voltage 1](unit-voltage-eq-one-of-angle-eq-zero.md)
- [Sine formula for the lossless sending-end real power](ac-branch-real-power-eq-mul-sin.md)
- [Receiving-end real power equals sending-end real power](receiving-real-power-eq-ac-branch-real-p.md)
- [Nodal AC real power is a signed sum of branch sine flows](node-real-power-eq-sum-mul-sin.md)
- [Total AC real power of the lossless network is zero](sum-node-real-power-eq-zero.md)
- [Reversing all branches negates the sending-end AC real power](ac-branch-real-power-reverse.md)

## Comparison of the AC and DC models

- [Per-branch cubic error of the DC flow for positive susceptances](abs-ac-branch-real-power-sub-dc-branch-f.md)
- [Nodal cubic error of the DC injection for positive susceptances](abs-node-real-power-sub-dc-injection-le.md)
- [Lossless DC flow model and its cubic error for positive susceptances](model-correct.md)

## Outside the lossless unit-magnitude model

- [Lossless sending-end real power with non-unit voltage magnitudes](real-power-scaled-voltage.md)
- [Sending-end real power of a conductance branch at unit magnitudes](real-power-conductance.md)
