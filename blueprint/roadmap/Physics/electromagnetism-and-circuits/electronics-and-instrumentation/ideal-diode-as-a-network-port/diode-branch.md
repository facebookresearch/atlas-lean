# Diode Branch

A diode with anode at node `a` and cathode at node `c` occupies network
branch `e` (in either orientation), and the passive branch current `i e`
(tail to head) is `s * diodeCurrent (s * v e)`, where
`s = ArcPortSigns.electricalIncidence tail head a e` is `+1` when the anode is the
branch tail and `-1` when the anode is the branch head.
