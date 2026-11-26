# Positional field lookup

Given a field list (pairs of a class and a field name) and the constructor arguments of an object, walks both lists together and returns the argument paired with the first field named `f`, or `none` if no paired field has that name, including when the argument list ends first. Used by the field projection rule (E-PROJ).
