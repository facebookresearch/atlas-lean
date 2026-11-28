# Rdv rot Residue false on no H

The rotated barrier-graph crossing `dcp_DualCutConnectsRot` fails for the wall configuration,
which has no horizontal crossing of `[0, 2]²` (`bcc_noH_wall`). So the hypothesis of
`dcp_rotatedDualVerticalCrossing_of_cutConnectsRot` does not follow from the absence of a
horizontal crossing.
