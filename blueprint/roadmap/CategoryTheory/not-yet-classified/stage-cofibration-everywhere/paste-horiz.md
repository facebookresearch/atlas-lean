# Paste horiz

Horizontally adjacent cell packets paste to a packet for their union.

The proof uses the stage cofibration `A(i,k) ⟶ A(i,l)` to choose the upper
pushout square.  `IsPushout.of_top` then identifies the lower square as the
cobase change of the first induced cofibration, so its composite with the
second induced cofibration is again a cofibration.
