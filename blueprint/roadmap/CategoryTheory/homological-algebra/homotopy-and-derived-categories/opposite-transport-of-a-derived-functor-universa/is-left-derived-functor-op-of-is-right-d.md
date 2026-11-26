# Opposite transport from a right derived functor to a left derived functor

Opposite transport from a right derived functor to a left derived functor.

Let L : C ⥤ D localize W and RF : D ⥤ H be a right derived functor with α : F → L ⋙ RF. Then
RF.op is a left derived functor along W.op, with comparison (Functor.opComp L RF).inv ≫
NatTrans.op α. The result uses opposite localization and the dual Kan-extension universal
property.
