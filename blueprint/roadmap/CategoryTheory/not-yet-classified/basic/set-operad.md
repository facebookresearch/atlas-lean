# Set Operad

Set operad as the Cartesian finite-tensor specialization of `OperadObj`.

`SetOperad` is `OperadObj (Type u)` via the canonical `FiniteTensor (Type u)`
instance given by dependent products. It inherits the unit, substitution, and
right/left unit and associativity laws from `OperadObj` without duplication.
