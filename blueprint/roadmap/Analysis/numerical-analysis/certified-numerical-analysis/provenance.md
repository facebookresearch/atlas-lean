# Provenance record of a numerical capstone

A provenance record of a numerical capstone has four fields: a string naming the unit system and the unit of the reported quantity, a string naming the version of the source data, a rational tolerance bounding the width of the certified bracket (so that every point of the bracket is within this distance of the true value), and a list of names of the library lemmas the certificate cites. The names are checked to exist when the record is built; that the proof uses them is not checked, and no dimensional analysis is performed.
