# Override check

The override check (OVERRIDE) for a method `m` with a signature (parameter classes and result class) against a class `D` passes when, if method type lookup finds a signature for `m` from `D`, that signature equals the given one exactly; it passes trivially when `D` has no such method.
