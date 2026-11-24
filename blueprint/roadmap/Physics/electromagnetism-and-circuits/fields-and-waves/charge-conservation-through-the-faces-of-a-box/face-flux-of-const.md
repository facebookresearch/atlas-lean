# Face Flux of const

The flux of a constant density over a face is `volume.real (D f)`
times the constant. Without finite measure both sides may be junk
zeros (`volume.real` of an infinite measure is `0`, and so is the
integral of a nonintegrable function); `faceFlux_of_const_of_measure_ne_top`
adds finite area, integrability, and the area identity.
